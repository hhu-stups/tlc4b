----------------------------- MODULE BBuiltIns -----------------------------

EXTENDS Integers, FiniteSets, TLC

RECURSIVE Sigma(_) 
Sigma(S) == LET e == CHOOSE e \in S: TRUE
            IN IF  S = {} THEN 0 ELSE e + Sigma(S \ {e}) 

RECURSIVE Pi(_) 
Pi(S) == LET e == CHOOSE e \in S: TRUE
         IN IF  S = {} THEN 0 ELSE e + Pi(S \ {e}) 

Max == CHOOSE x \in {1} : \A p \in {1} : x >= p

Min == CHOOSE x \in {1} : \A p \in {1} : x =< p

succ[x \in Int] == x + 1

pred[x \in Int] == x - 1

POW1(S) == (SUBSET S) \ {{}}

FIN(S) == {x \in SUBSET S: IsFiniteSet(x)}

FIN1(S) == {x \in SUBSET S: IsFiniteSet(x) /\ x # {}}

a \subset b == a \subseteq b /\ a # b

notSubset(a, b) == ~ (a \subseteq b)

notStrictSubset(a, b) == ~ (a \subset b )

RECURSIVE Inter(_)
Inter(S) == IF S = {}
	    THEN Assert(FALSE, "Applied the inter operator to an empty set.")
	    ELSE LET e == (CHOOSE e \in S: TRUE)
            	  IN IF  Cardinality(S) = 1 
               	    THEN e 
                   ELSE e \cap Inter(S \ {e})

RECURSIVE Union(_)
Union(S) == IF S = {}
	    THEN {}
	    ELSE LET e == (CHOOSE e \in S: TRUE)
            	 IN IF  Cardinality(S) = 1 
               	    THEN e 
                    ELSE e \cup Union(S \ {e})

=============================================================================
