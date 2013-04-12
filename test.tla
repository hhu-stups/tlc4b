---- MODULE test ----
EXTENDS Naturals
VARIABLES x
k == 100000
ASSUME k = 100000
Invariant == x \in 1 .. k
Init == x = 1
inc == x < k /\ x' = x + 1
reset == x = k /\ x' = 1
Next == \/ inc
	\/ reset
====