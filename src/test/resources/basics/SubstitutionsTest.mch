MACHINE FunctionsTest
VARIABLES x
INVARIANT x : 1..5
INITIALISATION x := 1
OPERATIONS
op1 = PRE 1 = 1 THEN x := 2 END;
op2 = LET a, b, c BE a = 1 & b : {1} & c = 2 IN x := 2 END;
op3 = SELECT 1=1 THEN x := 1 WHEN 1=1 THEN x:=2 ELSE x:= 3 END;
op4 = SELECT 1=1 THEN x := 1 WHEN 1=1 THEN x:=2 WHEN 1=1 THEN x:=3 ELSE x:= 4 END
END