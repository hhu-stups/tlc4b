MACHINE TraceValues
SETS S = {s1,s2,s3}
VARIABLES 
 numberValue,
 trueValue,
 falseValue,
 boolValue,
 intervalValue, 
 setValue,
 pairValue,
 sequenceValue,
 relationValue,
 recordValue,
 functionAsASet,
 enumerated,
 setOfTupleValue, /* Cartesian product */
 setCapValue,
 setCupValue,
 setDiffValue,
 lambdaValue,
 subsetValue,
 unionValue,
 structValue,
 functionType,
 stringValue,
 setPredValue
INVARIANT
 numberValue = 1
 & trueValue = TRUE
 & falseValue = FALSE
 & boolValue = BOOL
 & intervalValue = 1..10 
 & setValue = {1,2}
 & pairValue = (1, TRUE)
 & sequenceValue = [1,2,3,4]  
 & relationValue = {(1,2), (1,3)}
 & recordValue = rec(a: 1, b: TRUE)
 & functionAsASet = {(1, 1), (3,1)}
 & enumerated = {s1,s2,s3}
 & setOfTupleValue = S * S
 & setCapValue = {x,y| x : 1..2 & y: 1..2}
 & setCupValue = {x,y| x : 1..3 & y: 1..2}
 & setDiffValue = {x,y| x : 3..3 & y: 1..2}
 & lambdaValue = %x,y.(x: 1..3 & y : 1..3 | x+y)
 & subsetValue = POW(S)
 & unionValue = union({x| x : POW(BOOL) })
 & structValue = struct(a: 1..2, b: BOOL)
 & functionType = 1..3 --> BOOL
 & stringValue = "hello"
 & setPredValue = {x,y| x : 1..2 & y: 1..2}
INITIALISATION 
 numberValue := 1
 || trueValue := TRUE
 || falseValue := FALSE
 || boolValue := BOOL
 || intervalValue := 1..10
 || setValue := {1,2} 
 || pairValue := (1, TRUE) 
 || sequenceValue := [1,2,3,4] 
 || relationValue := {(1,2), (1,3)}
 || recordValue := rec(a: 1, b: TRUE)
 || functionAsASet := {(1, 1), (3,1)}
 || enumerated := {s1,s2,s3}
 || setOfTupleValue := S * S
 || setCapValue := {x,y| x : 1..2 & y: 1..2} /\ {x,y| x : 1..3 & y: 1..2}
 || setCupValue := {x,y| x : 1..2 & y: 1..2} \/ {x,y| x : 1..3 & y: 1..2}
 || setDiffValue := {x,y| x : 1..3 & y: 1..2} - {x,y| x : 1..2 & y: 1..2}
 || lambdaValue := %x,y.(x: 1..3 & y : 1..3 | x+y)
 || subsetValue := POW(S)
 || unionValue := union({x| x : POW(BOOL) })
 || structValue := struct(a: 1..2, b: BOOL)
 || functionType := 1..3 --> BOOL
 || stringValue := "hello"
 || setPredValue := {x,y| x : 1..2 & y: 1..2}
OPERATIONS foo = PRE 1 = 2 THEN skip END
END