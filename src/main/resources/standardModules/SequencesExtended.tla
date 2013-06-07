------------------------- MODULE SequencesExtended -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

LOCAL Range(f) == {f[x] :x \in DOMAIN f} 

Last(s) == s[Len(s)]

Front(s) == [i \in 1..(Len(s)-1) |-> s[i]]

Prepend(e, s) == [i \in 1..(Len(s)+1) |-> IF i = 1 THEN e ELSE s[i-1]]

BoundedSeq(S, n) == UNION{[1..x -> S]: x \in 0..n}

Seq1(S) == Seq(S) \ {<<>>}

ISeq(S) == UNION { {x \in [(1..n) -> S]: Cardinality(Range(x)) = Cardinality(DOMAIN x)} 
						: n \in 0..Cardinality(S)}

ISeqEleOf(S) == {x \in Seq(S): Len(x) = Cardinality(Range(x)) }

ISeq1(S) == ISeq(S) \ {<<>>} 

ISeq1EleOf(S) == {x \in Seq(S): x # <<>> /\ Len(x) = Cardinality(Range(x)) }

RECURSIVE Perm(_)
Perm(S) == IF S = {} 
           THEN {<<>>}
           ELSE LET ps == [x \in S |-> {Append(s, x): s \in Perm(S\{x})}]
                IN UNION {ps[x]: x \in S} 

Rev(s) == LET l == Len(s)
		  IN [i \in 1..l |-> s[l-i+1]]


RECURSIVE Conc(_)
Conc(S) == IF S = <<>>
           THEN <<>>
           ELSE Head(S) \o Conc(Tail(S))

TakeFirstElements(s, n) == IF Assert(n \in 0..Len(s), "Well defineness condition of take-first-operator is violated") 
                           THEN [i \in 1..n |-> s[i]] 
                           ELSE FALSE 

DropFirstElements(s, n) == IF Assert(n \in 0..Len(s), "Well defineness condition of drop-first-operator its violated") 
                           THEN [i \in 1..(Len(s)-n) |-> s[n + i]] 
                           ELSE FALSE 
=============================================================================
