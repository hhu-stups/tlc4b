------------------------ MODULE SequencesAsRelations ------------------------
EXTENDS FiniteSets, Naturals, Relations, FunctionsAsRelations

isRelSeq(x, S) == \A n \in 1..Cardinality(x): RelCall(x,n) \in S

RelSeqSet(x, S) == IF isRelSeq(x,S) THEN {x} ELSE {}


isRelSeq1(x, S) == x # {} /\ \A n \in 1..Cardinality(x): RelCall(x,n) \in S

RelSeqSet1(x, S) == IF isRelSeq1(x,S) THEN {x} ELSE {}

LOCAL ISeq(S) == UNION { {x \in [(1..n) -> S]: Cardinality(Range(x)) = Cardinality(DOMAIN x)} 
                        : n \in 0..Cardinality(S)}
                        
RelISeq(S) == {{<<n, x[n]>>:n \in 1..Len(x)} :x \in ISeq(S)}

RelISeq1(S) == RelISeq(S) \ {{}}

RelSeqSize(S) == Cardinality(S)

RelSeqConcat(a, b) == a \cup {<<x[1]+Cardinality(a), x[2]>> : x \in b} 

RelSeqPrepand(E, s) == {<<1,E>>} \cup {<<x[1]+1, x[2]>> : x \in s}

RelSeqAppend(s, E) == s \cup {<<Cardinality(s)+ 1,E>>}

RelSeqRev(s) == LET l == Cardinality(s)
                IN {<<l-x[1]+1, x[2]>>  : x \in s }                
RelSeqRev2(s) == LET l == Cardinality(s)
                 IN {<<i, RelCall(s,l-i+1)>>: i \in 1..l}
                
RelSeqFirst(s) == RelCall(s, 1)

RelSeqLast(s) == RelCall(s, Cardinality(s))

RelSeqFront(s) == {x \in s : x[1] # Cardinality(s)}
\*RelSeqFront2(s) == s \ {<<Cardinality(s), RelCall(s, Cardinality(s))>>}

RelSeqTail(s) == {<<x[1]-1,x[2]>> :x \in {x \in s : x[1] # 1}}

RECURSIVE RelSeqPerm(_)
RelSeqPerm(S) == IF S = {} 
           THEN {{}}
           ELSE LET ps == [x \in S |-> {RelSeqAppend(s, x): s \in RelSeqPerm(S\{x})}]
                IN UNION {ps[x]: x \in S} 


RECURSIVE RelSeqConc(_)
RelSeqConc(S) == IF S = {}
           THEN {}
           ELSE RelSeqConcat(RelSeqFirst(S), RelSeqConc(RelSeqTail(S)) )

RelSeqTakeFirstElements(s, n) == IF Assert(n \in 0..Cardinality(s), "Well defineness condition of take-first-operator is violated") 
                           THEN {x \in s: x[1] \leq n}
                           ELSE FALSE 

RelSeqDropFirstElements(s, n) == IF Assert(n \in 0..Cardinality(s), "Well defineness condition of drop-first-operator its violated") 
                           THEN {<<x[1]-n,x[2]>> :x \in {x \in s: x[1] > n}}
                           ELSE FALSE                 
=============================================================================