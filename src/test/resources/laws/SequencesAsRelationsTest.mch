MACHINE SequencesAsRelationsTest
VARIABLES x
INVARIANT x : 1..3
INITIALISATION x := 1
OPERATIONS
foo = PRE 1 = 1 THEN x := 2 END 
ASSERTIONS
 {} = [];
 {(1,1)} = [1]
 /*[] /: seq1({1,2});
 iseq({1,2}) ={[], [1], [2], [1, 2], [2, 1]};
 [1] : iseq({1,2});
 iseq1({1,2}) ={[1], [2], [1, 2], [2, 1]};
 [1] : iseq1({1,2});
 perm({1,2}) = {[1,2], [2,1]};
 rev([1,2,3]) = [3,2,1];
 conc([[1,2],[3],[4,5]]) = [1,2,3,4,5];
 [1,2,3,4] /|\ 3 = [1,2,3];
 [1,2,3,4] \|/ 3 = [4];
 1 -> [2,3] = [1,2,3];
 last([1,2]) = 2;
 front([1,2,3]) = [1,2]*/
END