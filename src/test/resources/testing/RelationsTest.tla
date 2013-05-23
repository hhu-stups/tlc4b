---- MODULE RelationsTest ----
EXTENDS Relations
VARIABLES x
Invariant == x = 1
Assertion1 == Relation({1}, {2}) = {{}, {<<1, 2>>}}
Assertion2 == RelDomain({<<1, 2>>}) = {1}
Assertion3 == RelDomain({<<<<1, 2>>, 3>>}) = {<<1, 2>>}
Assertion4 == RelRange({<<1, 2>>}) = {2}
Assertion5 == RelRange({<<<<1, 2>>, 3>>}) = {3}
Assertion6 == RelId({1, 2}) = {<<1, 1>>, <<2, 2>>}
Assertion7 == RelDomRes({1}, {<<1, 2>>, <<3, 4>>}) = {<<1, 2>>}
Assertion8 == RelDomSub({1}, {<<1, 2>>, <<3, 4>>}) = {<<3, 4>>}
Assertion9 == RelImage({<<3, TRUE>>}, {3}) = {TRUE}
Assertion10 == RelInverse({<<1, TRUE>>}) = {<<TRUE, 1>>}
Assertion11 == RelOverride({<<1, 2>>}, {<<1, 3>>}) = {<<1, 3>>}
Init == x = 1
foo == x' = 1

Next == \/ foo
====