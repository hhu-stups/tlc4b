------------------------ MODULE SequencesAsRelations ------------------------
EXTENDS FiniteSets, Naturals, Relations, FunctionsAsRelations

IsRelSeq(x, S) == \A n \in 1..Cardinality(x): RelCall(x,n) \in S
 \* Testing if x is a sequence with elements of the set S

RelSeqSet(x, S) == IF IsRelSeq(x,S) THEN {x} ELSE {}

IsRelSeq1(x, S) == x # {} /\ IsRelSeq(x, S)
 \* Testing if x is a non-empty sequence with elements of the set S
 
RelSeqSet1(x, S) == IF IsRelSeq1(x,S) THEN {x} ELSE {}

LOCAL ISeq(S) == UNION { {x \in [(1..n) -> S]: Cardinality(Range(x)) = Cardinality(DOMAIN x)} 
                        : n \in 0..Cardinality(S)}
                        
RelISeq(S) == {{<<n, x[n]>>:n \in 1..Len(x)} :x \in ISeq(S)}
 \* The set of all injective sequences with elements of S
 
RelISeq1(S) == RelISeq(S) \ {{}}
 \* The set of all non-empty injective sequences with elements of S

LOCAL SeqTest(s) == RelDomain(s) = 1..Cardinality(s)
 \* Testing if s is a sequence
 
RelSeqFirst(s) == IF SeqTest(s) 
    THEN RelCall(s, 1)
    ELSE Assert(FALSE, "Error: The argument of the first-operator should be a sequence.")
 \* The head of the sequence
 
RelSeqLast(s) == IF SeqTest(s) 
	THEN RelCall(s, Cardinality(s))
	ELSE Assert(FALSE, "Error: The argument of the last-operator should be a sequence.")
 \* The last element of the sequence

RelSeqSize(s) == IF SeqTest(s) 
	THEN Cardinality(s)
	ELSE Assert(FALSE, "Error: The argument of the size-operator should be a sequence.")
 \* The size of the sequence s
	
RelSeqTail(s) == IF SeqTest(s) 
    THEN {<<x[1]-1,x[2]>> : x \in {x \in s : x[1] # 1}}
    ELSE Assert(FALSE, "Error: The argument of the tail-operator should be a sequence.")
 \* The tail of the sequence s
    
RelSeqConcat(s1, s2) == IF SeqTest(s1) /\ SeqTest(s2)
    THEN s1 \cup {<<x[1]+Cardinality(s1), x[2]>> : x \in s2} 
    ELSE Assert(FALSE, "Error: The arguments of the concatenation-operator should be sequences.")
 \* The concatenation of sequence s1 and sequence s2
    
RelSeqPrepand(e, s) == IF SeqTest(s)
    THEN {<<1,e>>} \cup {<<x[1]+1, x[2]>> : x \in s}
    ELSE Assert(FALSE, "Error: The second argument of the prepend-operator should be a sequence.")
 \* The sequence obtained by inserting e at the front of sequence s. 
    
RelSeqAppend(s, e) == IF SeqTest(s)
    THEN s \cup {<<Cardinality(s)+ 1,e>>}
    ELSE Assert(FALSE, "Error: The first argument of the append-operator should be a sequence.")
 \* The sequence obtained by appending e to the end of sequence s.     

RelSeqReverse(s) == IF SeqTest(s)
    THEN {<<Cardinality(s)-x[1]+1, x[2]>>  : x \in s }   
    ELSE Assert(FALSE, "Error: The argument of the reverse-operator should be a sequence.")               
 \* The sequence obtained by reversing the order of the elements.
               
RelSeqFront(s) == IF SeqTest(s)
    THEN {x \in s : x[1] # Cardinality(s)}
    ELSE Assert(FALSE, "Error: The argument of the front-operator should be a sequence.")     
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
    IF SeqTest(s) /\ n \in 0..Cardinality(s)
    THEN {x \in s: x[1] \leq n}
    ELSE /\ Assert(n \in 0..Cardinality(s), 
             "The second argument of the take-first-operator is an invalid number.") 
         /\ Assert(FALSE, "Error: The first argument of the take-first-operator should be a sequence.") 
 \* The first n elements of s as a sequence
 
RelSeqDropFirstElements(s, n) == 
    IF SeqTest(s) /\ n \in 0..Cardinality(s)
    THEN {<<x[1]-n,x[2]>> :x \in {x \in s: x[1] > n}}
    ELSE /\ Assert(n \in 0..Cardinality(s),
    	     "The second argument of the drop-first-operator is an invalid number.")
         /\ Assert(FALSE, "Error: The first argument of the drop-first-operator should be a sequence.")              
  \* The last n elements of s as a sequence
=============================================================================