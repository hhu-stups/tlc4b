MACHINE Test
DEFINITIONS
 ASSERT_LTL_1 == "G(!a.({a:ID & a==aa} => F{a : xx}))"
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

