MACHINE SimpleForLog
VARIABLES i
INVARIANT i : 1..4
INITIALISATION i := 1
OPERATIONS inc = PRE i < 5 THEN i := succ(i) END
END