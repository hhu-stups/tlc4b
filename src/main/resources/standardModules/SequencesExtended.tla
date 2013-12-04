------------------------- MODULE SequencesExtended -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

LOCAL Range(f) == {f[x] :x \in DOMAIN f} 

Last(s) == s[Len(s)]
 \* The last element of the sequence s

Front(s) == [i \in 1..(Len(s)-1) |-> s[i]]
 \* The sequence s without its last element.

Prepend(e, s) == [i \in 1..(Len(s)+1) |-> IF i = 1 THEN e ELSE s[i-1]]
 \* The Sequence obtained by inserting e at the front of sequence s

Reverse(s) == LET l == Len(s)
              IN [i \in 1..l |-> s[l-i+1]]
\* Sequence s in reverse order

BoundedSeq(S, n) == UNION{[1..x -> S]: x \in 0..n}
 \* The set of sequences with maximum length n
 
Seq1(S) == Seq(S) \ {<<>>}
 \* The set of sequences without the empty sequence

ISeq(S) == 
    UNION {{x \in [(1..n) -> S]: Cardinality(Range(x)) = Cardinality(DOMAIN x)} 
					: n \in 0..Cardinality(S)}
 \* The set of injective sequences

ISeqEleOf(S) == {x \in Seq(S): Len(x) = Cardinality(Range(x)) }
 (* The set of injective sequences *)
 (* optimized to test if a certain sequence is in this set.*)
 
ISeq1(S) == ISeq(S) \ {<<>>} 
 \* The set of injective sequences without the empty sequence 
  
ISeq1EleOf(S) == {x \in Seq(S): x # <<>> /\ Len(x) = Cardinality(Range(x)) }
 (* The set of injective sequences without the empty sequence*)
 (* optimized to test if a certain sequence is in this set. *)

RECURSIVE Perm(_)
Perm(S) == IF S = {} 
           THEN {<<>>}
           ELSE LET ps == [x \in S |-> {Append(s, x): s \in Perm(S\{x})}]
                IN UNION {ps[x]: x \in S}
\* The set of permutations (bijective sequences)

RECURSIVE Conc(_)
Conc(S) == IF S = <<>>
           THEN <<>>
           ELSE Head(S) \o Conc(Tail(S))
 (* The sequence obtained by concatenating all sequences *)
 (* which are elements of the sequence S. *)          

TakeFirstElements(s, n) == 
    IF n \in 0..Len(s)
    THEN [i \in 1..n |-> s[i]] 
    ELSE Assert(n \in 0..Cardinality(s),
    	     "The second argument of the take-first-operator is an invalid number.")
 \* Taking the first n elements of the sequence s.                         

DropFirstElements(s, n) == 
    IF n \in 0..Len(s)
    THEN [i \in 1..(Len(s)-n) |-> s[n + i]] 
    ELSE Assert(n \in 0..Cardinality(s),
    	     "The second argument of the drop-first-operator is an invalid number.")
 \* Dropping the first n elements of the sequence s                           
=============================================================================
