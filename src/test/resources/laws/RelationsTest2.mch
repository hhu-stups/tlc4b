MACHINE RelationsTest2
VARIABLES x
INVARIANT x : 1..3
INITIALISATION x := 1
OPERATIONS
foo = PRE 1 = 1 THEN x := 2 END 
ASSERTIONS
 {1} <-> {2} = {{}, {(1,2)}};
 dom({(1,2)}) = {1};
 dom({(1,2,3)}) = {(1,2)};
 ran({(1,2)}) = {2};
 ran({(1,2,3)}) = {3};
 id({1,2}) = {(1,1),(2,2)};
 {1} <| {(1,2),(3,4)} = {(1,2)};
 {1} <<| {(1,2), (3,4)} = {(3,4)};
 {(3,TRUE)}[{3}] = {TRUE};
 {(1,TRUE)}~ = {(TRUE,1)};
 {(1,2)} <+ {(1,3)} ={(1,3)}
END
