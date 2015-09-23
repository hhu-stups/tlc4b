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
BPowerOf(a,b) == IF a = 0 /\ b = 0 THEN 1 ELSE a ^ b

BDivision(a,b) ==
  CASE a >= 0 /\ b > 0 -> a \div b
    [] a < 0 /\ b > 0 -> -((-a) \div b)
    [] a >= 0 /\ b < 0 -> -(a \div (-b))
    [] a < 0 /\ b < 0 -> (-a) \div (-b)
    [] Assert(b /= 0, "Error: Division by zero.") -> 0 \* dummy value
\* Rules from AtelierB reference manual (see page 40)

BModulo(a,b) ==
  IF Assert(a >= 0 /\ b > 0, "Error: Both operands of the modulo operator must be natural numbers.")
  THEN a % b
  ELSE 0 \* dummy value

RECURSIVE Sigma(_)
Sigma(S) ==
  IF S = {} THEN 0
  ELSE
    LET
      e == CHOOSE e \in S: TRUE
      newS == S \ {e}
    IN
      IF newS = {}
      THEN e[2]
      ELSE e[2] + Sigma(S \ {e})
 \* The sum of all second components of pairs which are elements of S

RECURSIVE Pi(_)
Pi(S) ==
    IF S = {} THEN 0
    ELSE
      LET
        e == CHOOSE e \in S: TRUE
        newS == S \ {e}
      IN
        IF newS = {}
        THEN e[2]
        ELSE e[2] * Pi(S \ {e})
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
Inter(S) ==
  IF Assert(S /= {}, "Error: Applied the inter operator to an empty set.")
	THEN
    LET e == (CHOOSE e \in S: TRUE)
    IN  IF  Cardinality(S) = 1
        THEN e
        ELSE e \cap Inter(S \ {e})
	ELSE {} \* dummy value
 \* The intersection of all elements of S.
=============================================================================
