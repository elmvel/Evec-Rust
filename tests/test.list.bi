:i count 22
:b shell 41
../target/debug/main ./dbg.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
5

:b stderr 0

:b shell 46
../target/debug/main ./inttypes.eve && ./b.out
:i returncode 0
:b stdout 66
Created executable b.out!
9223372036854775807
9223372036854775807

:b stderr 0

:b shell 45
../target/debug/main ./algebra.eve && ./b.out
:i returncode 0
:b stdout 90
Created executable b.out!
12
12
12
12
12
12
12
12
-12
-12
-12
-12
-12
-12
-12
-12
69
5701

:b stderr 0

:b shell 50
../target/debug/main ./redefinition.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 74
./redefinition.eve:9:9: error: Redefinition of variable y is not allowed!

:b shell 48
../target/debug/main ./assignment.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 71
./assignment.eve:14:5: error: Assignment expected s32, got u64 instead

:b shell 42
../target/debug/main ./bool.eve && ./b.out
:i returncode 0
:b stdout 42
Created executable b.out!
bool: 1
bool: 0

:b stderr 0

:b shell 46
../target/debug/main ./boolexpr.eve && ./b.out
:i returncode 0
:b stdout 101
Created executable b.out!
bool: 1
bool: 0
bool: 0
bool: 0
1111111111
bool: 1
bool: 1
bool: 1
bool: 0

:b stderr 0

:b shell 54
../target/debug/main ./boolexpr_enforce.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 52
./boolexpr_enforce.eve:7:9: error: Expected boolean

:b shell 48
../target/debug/main ./comparison.eve && ./b.out
:i returncode 0
:b stdout 82
Created executable b.out!
bool: 1
bool: 1
bool: 1
bool: 1
bool: 1
bool: 1
bool: 1

:b stderr 0

:b shell 40
../target/debug/main ./if.eve && ./b.out
:i returncode 0
:b stdout 36
Created executable b.out!
1
3
3
7
0

:b stderr 0

:b shell 49
../target/debug/main ./stackframe1.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 49
../target/debug/main ./stackframe2.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 61
./stackframe2.eve:10:9: error: No variable exits of name 'y'

:b shell 43
../target/debug/main ./while.eve && ./b.out
:i returncode 0
:b stdout 53
Created executable b.out!
10
9
8
7
6
5
4
3
2
1
0
420

:b stderr 0

:b shell 52
../target/debug/main ./break_continue.eve && ./b.out
:i returncode 0
:b stdout 58
Created executable b.out!
10
9
8
7
10
9
8
7
6
5
4
3
2
1
0

:b stderr 0

:b shell 61
../target/debug/main ./module.eve ./module_foo.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
69
1337
400

:b stderr 0

:b shell 84
../target/debug/main ./module2.eve ./module2_mod.eve ./module2_io_mod.eve && ./b.out
:i returncode 0
:b stdout 33
Created executable b.out!
420
69

:b stderr 57
warning: Ambiguous path `mod`, choosing the first one...

:b shell 47
../target/debug/main ./functions.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 54
../target/debug/main ./return_typecheck.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 81
./return_typecheck.eve:16:5: error: Expected to return bool, but got s32 instead

:b shell 44
../target/debug/main ./addrof.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
5

:b stderr 0

:b shell 51
../target/debug/main ./type_printing.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 78
./type_printing.eve:10:5: error: Expected to return s32, but got bool instead

:b shell 54
../target/debug/main ./deref_and_assign.eve && ./b.out
:i returncode 0
:b stdout 46
Created executable b.out!
0x7ffd17032cdc
5
69

:b stderr 0

:b shell 61
../target/debug/main ./pointer_type_annotation.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 82
./pointer_type_annotation.eve:5:9: error: Expected type *s32, but got s32 instead

