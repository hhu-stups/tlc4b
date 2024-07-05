MACHINE SubstitutionsTest
VARIABLES x, y
INVARIANT x : 1..10 & y : 1..10
INITIALISATION x := 1 ; y := x
OPERATIONS
op1 = PRE 1 = 1 THEN x := 2 END;
op2 = LET a, b, c BE a = 1 & b : {1} & c = 2 IN x := 2 END;
op3 = SELECT 1=1 THEN x := 1 WHEN 1=1 THEN x:=2 ELSE x:= 3 END;
op4 = SELECT 1=1 THEN x := 1 WHEN 1=1 THEN x:=2 WHEN 1=1 THEN x:=3 ELSE x:= 4 END;

op5 = BEGIN LET p BE p = 2 IN x:= p END END;

// test assert:
op6 = BEGIN x := 1 ; y := x + 1 END;
op7 = BEGIN x := 1 || y := x + 1 END;
op8 = SELECT x : 2..9 & y : 2..9 THEN x := y ; y := 1 END;
op9 = ANY z WHERE z = 5 & x : 2..9 & y : 2..9 THEN x := y || y := 1 END;
op10 = BEGIN x, y := x, x + 1 END;

// test becomes element of:
op11 = PRE x < 6 THEN x :: 4..6 ; y := x + 1 END;
op12 = PRE x < 6 THEN x :: 4..6 || y := x + 1 END;
op13 = PRE x < 6 THEN x := 1 ; y :: {x} END;
op14 = PRE x < 6 THEN x := 1 || y :: {x} END;

// test becomes such:
op15 = BEGIN x : (x : 4..6) ; y := x END;
op16 = BEGIN x : (x : 4..6) || y := x END;
op17 = BEGIN x := 1 ; y : (x = y) END;
op18 = BEGIN x := 1 || y : (x = y) END
END