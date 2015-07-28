------------------------------ MODULE ExternalFunctions ------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

--------------------------------------------------------------------------------------
                                (* Strings *)
RECURSIVE SPLIT1(_,_,_,_)
LOCAL SPLIT1(s,c,start,i) ==
    CASE i = Len(s)+1 -> IF i /= start
                         THEN <<SubSeq(s,start,i-1)>>
                         ELSE <<>>
    [] i+Len(c)-1 > Len(s) -> <<SubSeq(s,start,Len(s))>>
    [] SubSeq(s,i,i+Len(c)-1) = c -> IF i /= start
                                   THEN <<SubSeq(s,start,i-1)>> \o SPLIT1(s,c,i+Len(c),i+Len(c))
                                   ELSE <<>> \o SPLIT1(s,c,i+Len(c),i+Len(c))
    [] OTHER -> SPLIT1(s,c,start,i+1)

STRING_SPLIT(s, c) == SPLIT1(s,c,1,1)


LOCAL DIGIT_TO_STRING(x) ==
    CASE x = 0 -> "0"
    [] x = 1 -> "1"
    [] x= 2 -> "2"
    [] x = 3 -> "3"
    [] x = 4 -> "4"
    [] x= 5 -> "5"
    [] x= 6 -> "6"
    [] x= 7 -> "7"
    [] x=8 -> "8"
    [] x=9 -> "9"

RECURSIVE INT_TO_STRING1(_)
LOCAL INT_TO_STRING1(i) ==
  IF i < 10
  THEN DIGIT_TO_STRING(i)
  ELSE INT_TO_STRING1(i\div10) \o DIGIT_TO_STRING(i%10)

INT_TO_STRING(i) ==
  IF i < 0
  THEN "-" \o INT_TO_STRING1(-i)
  ELSE INT_TO_STRING1(i)

LOCAL Max(S) == CHOOSE x \in S : \A p \in S : x >= p
RECURSIVE SORT_SET(_)
SORT_SET(s) ==
  IF s = {}
  THEN {}
  ELSE LET max == Max(s)
       IN SORT_SET(s\{max}) \cup {<<Cardinality(s), max>>}

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

    RECURSIVE pow(_,_)
    pow(a,b) == IF b = 0 THEN 1 ELSE a * pow(a,b-1)

    RECURSIVE STRING_TO_INT1(_,_)
    STRING_TO_INT1(s, i) ==
      IF i = Len(s)
      THEN STRINGDIGIT_TO_INT(item(s,i))
      ELSE STRINGDIGIT_TO_INT(item(s,i)) * pow(10,Len(s)-i) + STRING_TO_INT1(s,i+1)
  IN
    IF item(str, 1) = "-"
    THEN -1 * STRING_TO_INT1(SubSeq(str,2,Len(str)),1)
    ELSE STRING_TO_INT1(str,1)

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
