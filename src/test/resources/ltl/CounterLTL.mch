MACHINE CounterLTL
DEFINITIONS
ASSERT_LTL_1 == "F {x = 10}";
ASSERT_LTL_2 == "G(not(deadlock))";
ASSERT_LTL_3 == "G(deterministic(Inc,Reset))";
VARIABLES x
INVARIANT
 x : 1..10
INITIALISATION x:=1
OPERATIONS
  Inc = PRE x < 10 THEN x:= x + 1 END;
  Reset = PRE x = 10 THEN x := 1 END
END