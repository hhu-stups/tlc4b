---- MODULE test ----
VARIABLES x, y
Invariant == x = 1 /\ y = 1
Init == x = 1 /\ y = 1
foo == x' = 1 /\ UNCHANGED <<y>>
Next == foo
====