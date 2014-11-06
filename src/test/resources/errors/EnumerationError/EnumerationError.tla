---- MODULE EnumerationError ----
EXTENDS Sequences
VARIABLES x
Invariant1 == x = <<1>>
Init == x \in Seq({1}) /\ x \o x = <<1, 1>>

Next == 1 = 2 /\ UNCHANGED <<x>>
====