MACHINE WelldefinednessError3
VARIABLES x
INVARIANT x : 1..10
INITIALISATION x := 1
OPERATIONS
foo = x := %x.(x = 1 | 1)(2)
END