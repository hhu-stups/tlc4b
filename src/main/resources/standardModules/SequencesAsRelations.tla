------------------------ MODULE SequencesAsRelations ------------------------
EXTENDS FiniteSets, Naturals, Relations, FunctionsAsRelations

IsRelSeq(x, S) == \A n \in 1..Cardinality(x): RelCall(x,n) \in S
 \* Testing if x is a sequence with elements of the set S

RelSeqSet(x, S) == IF IsRelSeq(x,S) THEN {x} ELSE {}

RelSeq(S) == {p \in SUBSET(Nat \times S):
    LET d == {q[1] : q \in p}
    IN /\ Cardinality(p) = Cardinality(d)
       /\ d = 1..Cardinality(d)}

IsRelSeq1(x, S) == x # {} /\ IsRelSeq(x, S)
 \* Testing if x is a non-empty sequence with elements of the set S

RelSeqSet1(x, S) == IF IsRelSeq1(x,S) THEN {x} ELSE {}

RelSeq1(S) == {p \in SUBSET(Nat \times S):
    LET d == {q[1] : q \in p}
    IN /\ Cardinality(p) > 0
       /\ Cardinality(p) = Cardinality(d)
       /\ d = 1..Cardinality(d)}


LOCAL ISeq(S) == UNION { {x \in [(1..n) -> S]: Cardinality(Range(x)) = Cardinality(DOMAIN x)}
                        : n \in 0..Cardinality(S)}

RelISeq(S) == {{<<n, x[n]>>:n \in 1..Len(x)} :x \in ISeq(S)}
 \* The set of all injective sequences with elements of S

RelISeqEleOf(S) == {p \in SUBSET(Nat \times S):
    LET d == {q[1] : q \in p}
    IN /\ Cardinality(p) = Cardinality(d)
       /\ d = 1..Cardinality(d)
       /\ Cardinality(p) = Cardinality(RelRange(p))}

RelISeq1(S) == RelISeq(S) \ {{}}
 \* The set of all non-empty injective sequences with elements of S

RelISeq1EleOf(S) == {p \in SUBSET(Nat \times S):
    LET d == {q[1] : q \in p}
    IN /\ Cardinality(p) > 0
       /\ Cardinality(p) = Cardinality(d)
       /\ d = 1..Cardinality(d)
       /\ Cardinality(p) = Cardinality(RelRange(p))}

LOCAL SeqTest(s) == RelDomain(s) = 1..Cardinality(s)
 \* Testing if s is a sequence

LOCAL WDcheck(val, condition, message) == IF Assert(condition, message) THEN val ELSE val

RelSeqFirst(s) ==
  WDcheck(RelCall(s, 1), SeqTest(s), "Error: The argument of the first-operator should be a sequence.")
 \* The head of the sequence

RelSeqLast(s) ==
  WDcheck(RelCall(s, Cardinality(s)), SeqTest(s), "Error: The argument of the last-operator should be a sequence.")
 \* The last element of the sequence

RelSeqSize(s) ==
  WDcheck(Cardinality(s), SeqTest(s),"Error: The argument of the size-operator should be a sequence.")
 \* The size of the sequence s

RelSeqTail(s) ==
  WDcheck({<<x[1]-1,x[2]>> : x \in {x \in s : x[1] # 1}}, SeqTest(s), "Error: The argument of the tail-operator should be a sequence.")
 \* The tail of the sequence s

RelSeqConcat(s1, s2) ==
  WDcheck(s1 \cup {<<x[1]+Cardinality(s1), x[2]>> : x \in s2} , SeqTest(s1) /\ SeqTest(s2), "Error: The arguments of the concatenation-operator should be sequences.")
 \* The concatenation of sequence s1 and sequence s2

RelSeqPrepand(e, s) ==
  IF  Assert(SeqTest(s), "Error: The second argument of the prepend-operator should be a sequence.")
  THEN {<<1,e>>} \cup {<<x[1]+1, x[2]>> : x \in s}
  ELSE {} \* dummy
 \* The sequence obtained by inserting e at the front of sequence s.

RelSeqAppend(s, e) ==
  WDcheck(
    s \cup {<<Cardinality(s)+ 1,e>>},
    SeqTest(s),
    "Error: The first argument of the append operator should be a sequence."
  )
 \* The sequence obtained by appending e to the end of sequence s.

RelSeqReverse(s) ==
    WDcheck(
      {<<Cardinality(s)-x[1]+1, x[2]>>  : x \in s },
      SeqTest(s),
      "Error: The argument of the 'rev' operator should be a sequence."
    )
 \* The sequence obtained by reversing the order of the elements.

RelSeqFront(s) ==
  WDcheck(
    {x \in s : x[1] # Cardinality(s)},
    SeqTest(s),
    "Error: The argument of the front-operator should be a sequence."
  )
 \* The front of the sequence s (all but last element)

RECURSIVE RelSeqPerm(_)
RelSeqPerm(S) == IF S = {}
           THEN {{}}
           ELSE LET ps == [x \in S |-> {RelSeqAppend(s, x): s \in RelSeqPerm(S\{x})}]
                IN UNION {ps[x]: x \in S}
 (* The set of bijective sequences (permutations) *)
 (* e.g. {<<1,2,3>>,<<2,1,3>>,<<2,3,1>>,<<3,1,2>>,<<3,2,1>>} for S = {1,2,3} *)

RECURSIVE RelSeqConc(_)
RelSeqConc(S) ==
    IF S = {}
    THEN {}
    ELSE RelSeqConcat(RelSeqFirst(S), RelSeqConc(RelSeqTail(S)) )
 (* The sequence obtained by concatenating all sequences *)
 (* which are elements of the sequence S. *)

RelSeqTakeFirstElements(s, n) ==
    IF
      /\ Assert(SeqTest(s), "Error: The first argument of the take-first-operator should be a sequence.")
      /\ Assert(n \in 0..Cardinality(s), "The second argument of the take-first-operator is an invalid number.")
    THEN {x \in s: x[1] \leq n}
    ELSE {} \* dummy
 \* The first n elements of s as a sequence

RelSeqDropFirstElements(s, n) ==
    IF  /\ Assert(n \in 0..Cardinality(s),
            "The second argument of the drop-first-operator is an invalid number.")
        /\ Assert(SeqTest(s), "Error: The first argument of the drop-first-operator should be a sequence.")
    THEN {<<x[1]-n,x[2]>> :x \in {x \in s: x[1] > n}}
    ELSE {} \* dummy
  \* The last n elements of s as a sequence
=============================================================================
