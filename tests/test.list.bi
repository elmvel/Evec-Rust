:i count 57
:b shell 54
../target/debug/main -Q $QBE_PATH ./dbg.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
5

:b stderr 0

:b shell 59
../target/debug/main -Q $QBE_PATH ./inttypes.eve && ./b.out
:i returncode 0
:b stdout 66
Created executable b.out!
9223372036854775807
9223372036854775807

:b stderr 0

:b shell 58
../target/debug/main -Q $QBE_PATH ./algebra.eve && ./b.out
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

:b shell 63
../target/debug/main -Q $QBE_PATH ./redefinition.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 74
./redefinition.eve:9:9: error: Redefinition of variable y is not allowed!

:b shell 61
../target/debug/main -Q $QBE_PATH ./assignment.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 71
./assignment.eve:14:5: error: Assignment expected s32, got u64 instead

:b shell 55
../target/debug/main -Q $QBE_PATH ./bool.eve && ./b.out
:i returncode 0
:b stdout 42
Created executable b.out!
bool: 1
bool: 0

:b stderr 0

:b shell 59
../target/debug/main -Q $QBE_PATH ./boolexpr.eve && ./b.out
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

:b shell 67
../target/debug/main -Q $QBE_PATH ./boolexpr_enforce.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 52
./boolexpr_enforce.eve:7:9: error: Expected boolean

:b shell 61
../target/debug/main -Q $QBE_PATH ./comparison.eve && ./b.out
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

:b shell 53
../target/debug/main -Q $QBE_PATH ./if.eve && ./b.out
:i returncode 0
:b stdout 36
Created executable b.out!
1
3
3
7
0

:b stderr 0

:b shell 62
../target/debug/main -Q $QBE_PATH ./stackframe1.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 62
../target/debug/main -Q $QBE_PATH ./stackframe2.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 61
./stackframe2.eve:10:9: error: No variable exits of name 'y'

:b shell 56
../target/debug/main -Q $QBE_PATH ./while.eve && ./b.out
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

:b shell 65
../target/debug/main -Q $QBE_PATH ./break_continue.eve && ./b.out
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

:b shell 74
../target/debug/main -Q $QBE_PATH ./module.eve ./module_foo.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
69
1337
400

:b stderr 0

:b shell 97
../target/debug/main -Q $QBE_PATH ./module2.eve ./module2_mod.eve ./module2_io_mod.eve && ./b.out
:i returncode 0
:b stdout 33
Created executable b.out!
420
69

:b stderr 57
warning: Ambiguous path `mod`, choosing the first one...

:b shell 60
../target/debug/main -Q $QBE_PATH ./functions.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 67
../target/debug/main -Q $QBE_PATH ./return_typecheck.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 81
./return_typecheck.eve:16:5: error: Expected to return bool, but got s32 instead

:b shell 57
../target/debug/main -Q $QBE_PATH ./addrof.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
5

:b stderr 0

:b shell 64
../target/debug/main -Q $QBE_PATH ./type_printing.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 78
./type_printing.eve:10:5: error: Expected to return s32, but got bool instead

:b shell 67
../target/debug/main -Q $QBE_PATH ./deref_and_assign.eve && ./b.out
:i returncode 0
:b stdout 33
Created executable b.out!
5
5
69

:b stderr 0

:b shell 74
../target/debug/main -Q $QBE_PATH ./pointer_type_annotation.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 82
./pointer_type_annotation.eve:5:9: error: Expected type *s32, but got s32 instead

:b shell 58
../target/debug/main -Q $QBE_PATH ./nullptr.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
(nil)

:b stderr 0

:b shell 64
../target/debug/main -Q $QBE_PATH ./ptr_functions.eve && ./b.out
:i returncode 0
:b stdout 35
Created executable b.out!
1337
420

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array1.eve && ./b.out
:i returncode 0
:b stdout 68
Created executable b.out!
{
{
1
2
3
}
}
{
{
6
9
}
{
4
2
}
{
9
9
}
}

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array2.eve && ./b.out
:i returncode 0
:b stdout 102
Created executable b.out!
{
1
2
3
}
{
{
1
2
3
}
}
{
{
6
9
}
{
4
2
}
{
9
9
}
}
{
{
1
2
3
}
}
101010101

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array3.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
1
2
3

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array4.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
{
4
6
9
4
}

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array5.eve && ./b.out
:i returncode 0
:b stdout 50
Created executable b.out!
{
1
2
3
}
{
69
1337
3
}

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array6.eve && ./b.out
:i returncode 0
:b stdout 58
Created executable b.out!
{
69
420
1337
}
{
69
420
1337
}

:b stderr 0

:b shell 57
../target/debug/main -Q $QBE_PATH ./array7.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 90
./array7.eve:10:11: error: Inferring array sizes is not supported in function parameters!

:b shell 63
../target/debug/main -Q $QBE_PATH ./return_check.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 91
./return_check.eve:7:8: error: This function does not always return, but should return s32

:b shell 58
../target/debug/main -Q $QBE_PATH ./slices1.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
1
2
3
1
2
3

:b stderr 0

:b shell 58
../target/debug/main -Q $QBE_PATH ./slices2.eve && ./b.out
:i returncode 0
:b stdout 66
Created executable b.out!
10000
1
2
3
20000
2
3
30000
1
2
40000
2

:b stderr 0

:b shell 56
../target/debug/main -Q $QBE_PATH ./defer.eve && ./b.out
:i returncode 0
:b stdout 34
Created executable b.out!
4
1
2
3

:b stderr 0

:b shell 72
../target/debug/main -Q $QBE_PATH ./slice_call_convention.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
1
2
3

:b stderr 0

:b shell 58
../target/debug/main -Q $QBE_PATH ./slices3.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
1
1
2
2
3
3

:b stderr 0

:b shell 62
../target/debug/main -Q $QBE_PATH ./slices4_abi.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
6

:b stderr 0

:b shell 62
../target/debug/main -Q $QBE_PATH ./defer_defer.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 77
./defer_defer.eve:4:11: error: Cannot defer here (did you try to nest them?)

:b shell 62
../target/debug/main -Q $QBE_PATH ./type_alias1.eve && ./b.out
:i returncode 0
:b stdout 26
Created executable b.out!

:b stderr 0

:b shell 68
../target/debug/main -Q $QBE_PATH ./type_alias2_redef.eve && ./b.out
:i returncode 1
:b stdout 0

:b stderr 70
./type_alias2_redef.eve:5:6: error: Type alias `str2` already exists!

:b shell 58
../target/debug/main -Q $QBE_PATH ./strings.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
32
32

:b stderr 0

:b shell 56
../target/debug/main -Q $QBE_PATH ./usize.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 64
../target/debug/main -Q $QBE_PATH ./slice_methods.eve && ./b.out
:i returncode 0
:b stdout 30
Created executable b.out!
2
5

:b stderr 0

:b shell 65
../target/debug/main -Q $QBE_PATH ./struct_pointer.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
3

:b stderr 0

:b shell 62
../target/debug/main -Q $QBE_PATH ./hello_world.eve && ./b.out
:i returncode 0
:b stdout 38
Created executable b.out!
Hello world

:b stderr 0

:b shell 66
../target/debug/main -Q $QBE_PATH ./string_escaping.eve && ./b.out
:i returncode 0
:b stdout 103
Created executable b.out!
Hello from std io!
This is also a new line!
This C string is cut off early! 

:b stderr 0

:b shell 74
../target/debug/main -Q $QBE_PATH ./malloc_free_and_voidptr.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
3

:b stderr 0

:b shell 67
../target/debug/main -Q $QBE_PATH ./nullptr_equality.eve && ./b.out
:i returncode 0
:b stdout 42
Created executable b.out!
bool: 0
bool: 1

:b stderr 0

:b shell 55
../target/debug/main -Q $QBE_PATH ./cast.eve && ./b.out
:i returncode 0
:b stdout 29
Created executable b.out!
69

:b stderr 0

:b shell 59
../target/debug/main -Q $QBE_PATH ./implicit.eve && ./b.out
:i returncode 0
:b stdout 26
Created executable b.out!

:b stderr 0

:b shell 60
../target/debug/main -Q $QBE_PATH ./implicit2.eve && ./b.out
:i returncode 0
:b stdout 282
Created executable b.out!
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001
69
69
69
69
69
69
69
1000000001

:b stderr 0

:b shell 66
../target/debug/main -Q $QBE_PATH ./slice_init_list.eve && ./b.out
:i returncode 0
:b stdout 33
Created executable b.out!
Hello!

:b stderr 0

:b shell 63
../target/debug/main -Q $QBE_PATH ./rule110_stub.eve && ./b.out
:i returncode 0
:b stdout 28
Created executable b.out!
1

:b stderr 0

:b shell 69
../target/debug/main -Q $QBE_PATH ./array_default_init.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
0
0
0

:b stderr 0

:b shell 65
../target/debug/main -Q $QBE_PATH ./constant_array.eve && ./b.out
:i returncode 0
:b stdout 32
Created executable b.out!
0
0
0

:b stderr 0

:b shell 72
../target/debug/main -Q $QBE_PATH ./nested_array_constant.eve && ./b.out
:i returncode 0
:b stdout 40
Created executable b.out!
{
{
1
2
3
}
}

:b stderr 0

