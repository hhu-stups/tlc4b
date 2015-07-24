MACHINE ExternalFunctionsTest
DEFINITIONS
  printf(format_string,value) == TRUE=TRUE;
  EXTERNAL_PREDICATE_printf(T) == STRING*T;
  INT_TO_STRING(S) == "0";
  EXTERNAL_FUNCTION_INT_TO_STRING == (INTEGER --> STRING);
  STRING_SPLIT(x,y) == ["foo"];
  EXTERNAL_FUNCTION_STRING_SPLIT == ((STRING*STRING) --> (INTEGER<->STRING));
  EXTERNAL_FUNCTION_REC(A,B) == (STRING * A)-->B;
  REC(F,A) == {};
  EXTERNAL_FUNCTION_REC_LET(A) == (STRING * A)-->A;
  REC_LET(F,A) == {};

  STRING_APPEND(x,y) == "str";
  EXTERNAL_FUNCTION_STRING_APPEND == (STRING*STRING) --> STRING;

ABSTRACT_CONSTANTS SORT_SET
PROPERTIES
  SORT_SET: POW(INTEGER) <-> POW(INTEGER*INTEGER) &
  SORT_SET = REC_LET("SORT_SET",%x.(x={}|<>) \/ %x.(x:POW1(INTEGER)|REC("SORT_SET",x-{max(x)})<-max(x)))
ASSERTIONS
  printf("result", 2);

  INT_TO_STRING(123) = "123";
  INT_TO_STRING(-123) = "-123";
  STRING_SPLIT("foo bar", " ") = ["foo", "bar"];
  STRING_SPLIT(" foo", " ") = ["foo"];
  STRING_SPLIT("foo||bar", "||") = ["foo", "bar"];
  SORT_SET({4,2,3,1}) = [1,2,3,4];
  SORT_SET({}) = [];
  STRING_APPEND("a","bc") = "abc";
  STRING_APPEND("abc","") = "abc";
  STRING_APPEND("","abc") = "abc";
  STRING_APPEND("","") = ""

END
