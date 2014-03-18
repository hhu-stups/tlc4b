MACHINE FairnessCounter
DEFINITIONS
ASSERT_LTL_1 == "WF(Reset) & WF(Inc) =>  F {x = 0}"
VARIABLES x
INVARIANT
 x : 0..20
INITIALISATION x:=1
OPERATIONS
  Inc = PRE x < 12 THEN x:= x + 1 END;
  Reset = PRE x >= 10 THEN x := 0 END;
  doNothing = skip
END