MACHINE StatePropertyViolation
DEFINITIONS
 ASSERT_LTL_1 == "!a.({a:ID} => {1=2})"
SETS
 ID={aa,bb}
CONSTANTS iv
PROPERTIES
 iv:ID
VARIABLES xx
INVARIANT
 xx:POW(ID)
INITIALISATION xx:={}
OPERATIONS
  Set(yy) = SELECT yy:ID & yy /:xx THEN xx:= xx \/ {yy} END
END
