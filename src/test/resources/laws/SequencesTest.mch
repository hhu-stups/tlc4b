MACHINE SequencesTest
VARIABLES x
INVARIANT x : 1..3
INITIALISATION x := 1
OPERATIONS
foo = PRE 1 = 1 THEN x := 2 END 
ASSERTIONS
 [1,2,3] = %x.(x: {1,2,3}|x);
 []	= <>;
 [1] : seq({1,2,3});
 size([1,2,3]) = 3;
 [1,2] ^ [3] = [1,2,3];
 [1,2] <- 3 = [1,2,3];
 first([1,2]) = 1;
 tail([1,2,3]) = [2,3]
END