MACHINE ELSEIF
VARIABLES x,y,z,c
INVARIANT x : {1,4} & y : {1,2} & z : {1,3} & c : 1..3
INITIALISATION x,y,z,c := 1,1,1,1
OPERATIONS
 foo = IF c=1 THEN x:= 1 ELSIF c=2 THEN y:= 2 ELSIF c=3 THEN z:= 3 ELSE x:= 4 END;
 set2 = BEGIN c :: 1..3 END
END