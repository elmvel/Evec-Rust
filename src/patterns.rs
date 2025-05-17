// Interpreted from https://github.com/yorickpeterse/pattern-matching-in-rust/blob/main/jacobs2021/src/lib.rs
// Implementation mostly modelled from source, yet interpreted for a richer understanding

use std::collections::HashMap;

use crate::lexer::{Token, Location};
use crate::ast::*;
use crate::ir::TempValue;
use crate::gen::Generator;
use crate::Compiletime;

// The body of the branch, what code will be run
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    pub bindings: Vec<(Expr, TempValue)>,
    pub body: Vec<Stmt>,
}

// One arm of many branches in a match statement
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Row {
    pub cols: Vec<Column>,
    pub guard: Option<Expr>, // @bool
    pub body: Body,
}

impl Row {
    fn new(cols: Vec<Column>, guard: Option<Expr>, body: Body) -> Self {
        Self { cols, guard, body }
    }

    fn remove_column(&mut self, variable: &TempValue) -> Option<Column> {
        self.cols
            .iter()
            .position(|c| &c.variable == variable)
            .map(|idx| self.cols.remove(idx))
    }
}

// Matching of ONE variable in a row
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Column {
    pub variable: TempValue,
    pub pattern: Pattern,
}

impl Column {
    fn new(variable: TempValue, pattern: Pattern) -> Self {
        Self { variable, pattern }
    }
}

// The actual case to test
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Case {
    pub expr: Expr, // The constructor to test against
    pub arguments: Vec<TempValue>, // Hard to tell the purpose of this one?
    pub body: Decision,
}

impl Case {
    fn new(
        expr: Expr,
        arguments: Vec<TempValue>,
        body: Decision,
    ) -> Self {
        Self { expr, arguments, body }
    }
}

// The decision tree compiled from a list of match cases
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decision {
    // The pattern was matched, continue with the body
    Match(Body),

    // A pattern is missing
    Failure,

    // Run the body only if the guard passes
    // (condition, success_code, "decision tree to evaluate on failure")
    Conditional(Expr, Body, Box<Decision>),

    // Selection statement
    // (variable, "cases to test against", "fallback default if no case matched")
    Switch(TempValue, Vec<Case>, Option<Box<Decision>>),
}

// Storing diagnostic info
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct MatchMeta {
    pub missing: bool, // Are we missing patterns?
    pub reachable: Vec<usize>, // I assume to be indices of reachable patterns, not in this vector are redundant patterns
}

// "Compiled Result" from the paper -> take it to the backend
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Match {
    pub tree: Decision,
    pub meta: MatchMeta,
}

// Used to construct information about missing patterns
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    pub variable: TempValue,
    pub name: String,
    pub args: Vec<TempValue>,
}

// patterns.rs 

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    Binding(Expr), // Ident
    Literal(Expr), // number, string, bool
    Range(Expr), // range, special semantics when matching with a number
    Or(Vec<Pattern>), // Multiple patterns, such as <pat> | <pat>
    Sink, // _
    Rest, // .. IMPORTANT could be bound with 'as <ID>' (used in slices, tuples, structs)
    // TODO: Slice(Expr?), => [a, .., b], [], [a, b, c], [head, .. as tail]
}

impl Pattern {
    pub fn into_cols(self, name: Expr, comptime: &mut Compiletime, gen: &mut Generator) -> Vec<Column> {
        let mut cols = Vec::new();
        let tv = gen.emit_expr(comptime, name, None).unwrap();
        cols.push(Column {
            variable: tv,
            pattern: self
        });
        cols
    }
//     pub fn irrefutable(&self) -> bool {
//         match self {
//             Pattern::Binding(..) => true,
//             Pattern::Sink => true,
//             _ => false,
//         }
//     }
}

//////////// Match Preprocess ////////////

// Expand rows containing OR patterns into separate rows with the same body
fn expand_or_patterns(rows: &mut Vec<Row>) {
    // First, check if we have any OR patterns at all to avoid allocations if unnecessary
    if !rows
        .iter()
        .any(|r| r.cols.iter().any(|c| matches!(c.pattern, Pattern::Or(_))))
    {
        return;
    }

    // We will store all new rows here until no more OR patterns are found
    let mut new_rows = Vec::with_capacity(rows.len());
    // This is true to achieve "do-while" functionality
    let mut found = true;

    while found {
        found = false;

        for row in rows.drain(..) {
            // Find the first column containing an OR pattern
            let res = row.cols.iter().enumerate().find_map(|(idx, col)| {
                if let Pattern::Or(pats) = &col.pattern {
                    Some((idx, col.variable.clone(), pats))
                } else {
                    None
                }
            });

            if let Some((idx, var, pats)) = res {
                found = true;

                // This creates a new row for each OR pattern,
                // if other columns contain OR patterns, they will
                // be hit on future loop iterations
                for pat in pats {
                    let mut new_row = row.clone();
                    new_row.cols[idx] = Column::new(var.clone(), pat.clone());
                    new_rows.push(new_row);
                }
            } else {
                // Otherwise, keep it as is
                new_rows.push(row);
            }
        }

        std::mem::swap(rows, &mut new_rows);
    }
}

//////////// Match Compile ////////////

pub struct Transformer {
    pub meta: MatchMeta,
}

impl Transformer {
    pub fn compile_match(&mut self, comptime: &mut Compiletime, rows: Vec<Row>) -> Match {
        Match {
            tree: self.compile_rows(comptime, rows),
            meta: self.meta.clone(),
        }
    }

    fn compile_rows(&mut self, comptime: &mut Compiletime, mut rows: Vec<Row>) -> Decision {
        if rows.is_empty() {
            // If we're empty we're definitely missing patterns
            self.meta.missing = true;
            return Decision::Failure;
        }

        // TODO: supporting OR patterns
        // expand_or_patterns(&mut rows);

        for row in &mut rows {
            // Move any variable patterns into a binding in the body of the match arm
            // (Since these patterns are irrefutable)
            self.move_variable_patterns(row);
        }

        // If the first row has no columns, then it is irrefutable
        if rows.first().map_or(false, |r| r.cols.is_empty()) {
            let row = rows.remove(0);

            // TODO: I need to put something here to indicate the reachable row... I did not expect
            // the lib.rs to put in the ast of the body...?
            self.meta.reachable.push(69);

            // Can decide right here, right now (since the pattern is irrefutable)
            return if let Some(guard) = row.guard {
                // A-ha! if we have a guard, it still may not be irrefutable!
                // Thus, we continue the decision tree recursively
                Decision::Conditional(
                    guard,
                    row.body,
                    Box::new(self.compile_rows(comptime, rows))
                )
            } else {
                Decision::Match(row.body)
            };
        }

        // If we don't have an irrefutable pattern, decide which variable
        // we should test against first
        let branch_var = self.branch_variable(&rows);

        match branch_var.typ {
            Type::U64 |
            Type::U32 |
            Type::U16 |
            Type::U8  |
            Type::S64 |
            Type::S32 |
            Type::S16 |
            Type::S8  => {
                // Single out integer cases
                let (cases, fallback) = self.compile_int_cases(comptime, rows, branch_var.clone());
                Decision::Switch(branch_var, cases, Some(fallback))
            },
            Type::Bool => {
                // TODO: I have no clue wtf this is
                // For booleans I assume the cases are pretty tightly thin, so
                // we can narrow it down?
                let cases = vec![
                    (Expr::Bool(Token::True(ldef!())), Vec::new(), Vec::new()),
                    (Expr::Bool(Token::False(ldef!())), Vec::new(), Vec::new()),
                ];

                Decision::Switch(
                    branch_var.clone(),
                    self.compile_expr_cases(comptime, rows, branch_var, cases),
                    None,
                )
            },
            _ => todo!("Support other types!")
        }
    }

    fn compile_int_cases(
        &mut self,
        comptime: &mut Compiletime,
        rows: Vec<Row>,
        branch_var: TempValue
    ) -> (Vec<Case>, Box<Decision>) {
        // TODO: what is this
        let mut raw_cases: Vec<(Expr, Vec<TempValue>, Vec<Row>)> = Vec::new();
        // TODO: what is this
        let mut fallback_rows = Vec::new();
        // TODO: REALLY what is this
        // I dont like this whole constructor notion,
        // so this might seem redundant but its the most sensible atm
        let mut tested: HashMap<(Expr, Expr), usize> = HashMap::new();

        for mut row in rows {
            if let Some(col) = row.remove_column(&branch_var) {
                let (key, expr) = match col.pattern {
                    // TODO: whaat the fuck is this
                    // Ok I partially get it, we always test a range but for one value we just duplicate it
                    Pattern::Literal(ref expr @ Expr::Number(ref token)) =>
                        ((expr.clone(), expr.clone()), expr.clone()),
                    Pattern::Range(Expr::Range(_, lhs, rhs)) => {
                        // ((start, stop), Constructor::Range(start, stop))
                        todo!("ok I really don't know how to resolve this one")
                    },
                    _ => unreachable!(),
                };

                // TODO: I really don't understand this part
                if let Some(index) = tested.get(&key) {
                    raw_cases[*index].2.push(row.clone());
                }

                // TODO: this case test refers to this raw case?
                tested.insert(key, raw_cases.len());

                // TODO: huh?
                let mut rows = fallback_rows.clone();

                rows.push(row);

                // Push a case with an expr, no arguments, and these rows
                raw_cases.push((expr, Vec::new(), rows));
            } else {
                // I don't get any of this lol
                // This is for if we have no instance of the branch_var in this row,
                // so we may need to test against these rows in case of failure
                for (_, _, rows) in &mut raw_cases {
                    rows.push(row.clone());
                }

                fallback_rows.push(row);
            }
        }

        // The final cases to run as tests
        let cases = raw_cases
            .into_iter()
            .map(|(expr, vars, rows)| {
                Case::new(expr, vars, self.compile_rows(comptime, rows))
            })
            .collect();

        // Return the final cases to actually compile, and the
        // fallback rows in case of a failure
        (cases, Box::new(self.compile_rows(comptime, fallback_rows)))
    }

    fn compile_expr_cases(
        &mut self,
        comptime: &mut Compiletime,
        rows: Vec<Row>,
        branch_var: TempValue,
        mut cases: Vec<(Expr, Vec<TempValue>, Vec<Row>)>,
    ) -> Vec<Case> {
        todo!("compile_expr_cases")
    }

    // Moves variable-only patterns/tests into the right-hand side/body of a
    // case.
    //
    // This turns cases like this:
    //
    //     case foo -> print(foo)
    //
    // Into this:
    //
    //     case -> {
    //       let foo = it
    //       print(foo)
    //     }
    //
    // Where `it` is a variable holding the value `case foo` is compared
    // against, and the case/row has no patterns (i.e. always matches).
    fn move_variable_patterns(&self, row: &mut Row) {
        // This is like a filter but for Vec, not Iter
        row.cols.retain(|col| {
            if let Pattern::Binding(bind @ Expr::Ident(..)) = &col.pattern {
                // If this pattern is a variable binding,
                // push it as a prelude binding for the body...
                row.body.bindings.push((bind.clone(), col.variable.clone()));
                false
            } else {
                // ...Otherwise, ignore
                true
            }
        })
    }

    // Given a row, returns the variable within the row that is referred to the most
    // by all rows
    fn branch_variable(&self, rows: &[Row]) -> TempValue {
        // Where we store the counts per row
        let mut counts = HashMap::<TempValue, usize>::new();

        for row in rows {
            for col in &row.cols {
                // Increment the entry or set to 1 if it exists
                // (cause we set to 0 and immediately increment)
                *counts.entry(col.variable.clone()).or_insert(0) += 1;
            }
        }

        // Just a fancy way of getting the maximum referred to variable
        rows[0]
            .cols
            .iter()
            .map(|col| col.variable.clone())
            .max_by_key(|var| counts[var])
            .unwrap()
    }
}
