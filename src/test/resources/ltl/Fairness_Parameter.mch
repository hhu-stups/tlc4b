MACHINE Fairness_Parameter
DEFINITIONS
ASSERT_LTL_1 == "WF(Step) => F{x > 4}"
VARIABLES x
INVARIANT
 x : 1..10
INITIALISATION x := 1
OPERATIONS
  Step(p) = PRE p : 5..10 THEN x := p END;
  sk = skip
END

