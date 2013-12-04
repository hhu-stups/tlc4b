MACHINE Test
VARIABLES a, b, c, d
INVARIANT
 a : ((1..2) --> 1..10) \/ ((1..3) --> 1..10)
& b : ((1..2)*(1..2) --> 1..10)
& c : (1..3) <-> 1..10
& d : (1..3)*(1..3) <-> 1..10
INITIALISATION 
 a := %x.(x : 1..2 | x)
|| b:= %x,y.(x : 1..2 & y : 1..2 | x + y )
|| c := %x.(x : 1..2 | x)
|| d := %x,y.(x : 1..2 & y : 1..2 | x + y)
OPERATIONS
 Set1 = a(1) := 10;
 Set11 = a(3) := 10;
 Set2 = b(1,2) := 10;
 Set3 = c(1) := 10;
 Set31 = c(3) := 10;
 Set4 = d(1,2) := 10;
 Set41 = d(1,3) := 10;
 Set42 = d(3,1) := 10;
 Set43 = d(3,3) := 10
END