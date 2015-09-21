------------------------------ MODULE ExternalFunctions ------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

--------------------------------------------------------------------------------------
                                (* Strings *)

LOCAL SPLIT1[s \in STRING, c \in STRING, start \in Nat, i \in Nat] ==
    CASE i = Len(s)+1 -> IF i /= start
                         THEN <<SubSeq(s,start,i-1)>>
                         ELSE <<>>
    [] i+Len(c)-1 > Len(s) -> <<SubSeq(s,start,Len(s))>>
    [] SubSeq(s,i,i+Len(c)-1) = c -> IF i /= start
                                   THEN <<SubSeq(s,start,i-1)>> \o SPLIT1[s,c,i+Len(c),i+Len(c)]
                                   ELSE <<>> \o SPLIT1[s,c,i+Len(c),i+Len(c)]
    [] OTHER -> SPLIT1[s,c,start,i+1]

STRING_SPLIT(s, c) == SPLIT1[s,c,1,1]


INT_TO_STRING(i) == ToString(i)

LOCAL Max(S) == CHOOSE x \in S : \A p \in S : x >= p

SORT_SET(s2)==
  LET
    SORT_SET_Recursive[s \in SUBSET Int] ==
      IF s = {}
      THEN {}
      ELSE LET max == Max(s)
           IN SORT_SET_Recursive[s\{max}] \cup {<<Cardinality(s), max>>}
  IN SORT_SET_Recursive[s2]

STRING_APPEND(a,b) == a \o b

STRING_TO_INT(str) ==
  LET
    STRINGDIGIT_TO_INT(x) ==
      CASE x = "0" -> 0
        [] x= "1" -> 1
        [] x= "2" -> 2
        [] x= "3" -> 3
        [] x= "4" -> 4
        [] x= "5" -> 5
        [] x= "6" -> 6
        [] x= "7" -> 7
        [] x= "8" -> 8
        [] x= "9" -> 9

    item(s,i) == SubSeq(s,i,i)

    STRING_TO_INT1[s \in STRING, i \in Nat] ==
      IF i = Len(s)
      THEN STRINGDIGIT_TO_INT(item(s,i))
      ELSE STRINGDIGIT_TO_INT(item(s,i)) * 10^(Len(s)-i) + STRING_TO_INT1[s,i+1]
  IN
    IF item(str, 1) = "-"
    THEN -1 * STRING_TO_INT1[SubSeq(str,2,Len(str)),1]
    ELSE STRING_TO_INT1[str,1]

DECIMAL_TO_INT(s) ==
    STRING_TO_INT(
      STRING_APPEND(
        (STRING_SPLIT(s,"."))[1]
        ,(STRING_SPLIT(s,"."))[2]
      )
    )
-----------------------------------------------------------------------------
printf(s,v) == PrintT(s) /\ PrintT(v)

=============================================================================
