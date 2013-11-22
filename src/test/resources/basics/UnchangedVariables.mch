MACHINE test
VARIABLES a,b,c, func, rela
INVARIANT a = 1 & b = 1 & c = 1 & func : 1..3 +-> 1..10  & rela : 1..3 <-> 1..3
INITIALISATION a,b,c := 1,1,1 || func := %p.(p: {1}| 1) || rela := {(1,1)}
OPERATIONS 
IfElseOp1 = IF 1 = 1 THEN a := 1 END;
IfThenElse = IF a = 1 THEN b:= 1 ELSE c := 1 END;
Choice = CHOICE a := 1 OR b:= 1 END;
FuncOp = func(1):= 3;
FuncOp2 = func(2):= 4;
RelOp = rela(1):= 1
END