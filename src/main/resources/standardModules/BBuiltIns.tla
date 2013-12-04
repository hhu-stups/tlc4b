----------------------------- MODULE BBuiltIns -----------------------------
EXTENDS Integers, FiniteSets, TLC

Max(S) == CHOOSE x \in S : \A p \in S : x >= p
 \* The largest element of the set S
 
Min(S) == CHOOSE x \in S : \A p \in S : x =< p
 \* The smallest element of the set S
 
succ[x \in Int] == x + 1
 \* The successor function

pred[x \in Int] == x - 1
 \* The predecessor function
 
RECURSIVE Sigma(_) 
Sigma(S) == LET e == CHOOSE e \in S: TRUE
            IN IF  S = {} THEN 0 ELSE e[2] + Sigma(S \ {e}) 
 \* The sum of all second components of pairs which are elements of S

RECURSIVE Pi(_) 
Pi(S) == LET e == CHOOSE e \in S: TRUE
         IN IF  S = {} THEN 0 ELSE e[2] + Pi(S \ {e}) 
 \* The product of all second components of pairs which are elements of S

Pow1(S) == (SUBSET S) \ {{}}
 \* The set of non-empty subsets

Fin(S) == {x \in SUBSET S: IsFiniteSet(x)}
 \* The set of all finite subsets.
 
Fin1(S) == {x \in SUBSET S: IsFiniteSet(x) /\ x # {}}
 \* The set of all non-empty finite subsets
 
S \subset T == S \subseteq T /\ S # T
 \* The predicate becomes true if S is a strict subset of T

NotSubset(S, T) == ~ (S \subseteq T)
 \* The predicate becomes true if S is not a subset of T

NotStrictSubset(S, T) == ~ (S \subset T)
  \* The predicate becomes true if S is not a strict subset of T
  
RECURSIVE Inter(_)
Inter(S) == IF S = {}
	    THEN Assert(FALSE, "Error: Applied the inter operator to an empty set.")
	    ELSE LET e == (CHOOSE e \in S: TRUE)
            	  IN IF  Cardinality(S) = 1 
               	    THEN e 
                   ELSE e \cap Inter(S \ {e})
 \* The intersection of all elements of S.
=============================================================================
