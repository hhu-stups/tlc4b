---- MODULE RelationsTest ----
EXTENDS Relations
Assertion1 == Relations({1}, {2}) = {{}, {<<1, 2>>}}
Assertion2 == RelDomain({<<1, 2>>}) = {1}
Assertion3 == RelDomain({<<<<1, 2>>, 3>>}) = {<<1, 2>>}
Assertion4 == RelRange({<<1, 2>>}) = {2}
Assertion5 == RelRange({<<<<1, 2>>, 3>>}) = {3}
Assertion6 == RelId({1, 2}) = {<<1, 1>>, <<2, 2>>}
Assertion7 == RelDomRes({1}, {<<1, 2>>, <<3, 4>>}) = {<<1, 2>>}
Assertion8 == RelDomSub({1}, {<<1, 2>>, <<3, 4>>}) = {<<3, 4>>}
Assertion9 == RelImage({<<3, TRUE>>}, {3}) = {TRUE}
Assertion10 == RelInverse({<<1, TRUE>>}) = {<<TRUE, 1>>}
Assertion11 == {<<1, 1>>} \in RelTotalFuncEleOf({1}, {1})
Assertion12 == RelIParFunc({3, 4}, {5}) = {{}, {<<3, 5>>}, {<<4, 5>>}}
Assertion13 == {} \in RelParFunc({1}, {1})
Assertion14 == RelOver({<<1, 2>>}, {<<1, 3>>}) = {<<1, 3>>}
Assertion15 == iseq({TRUE}) = {{}, {<<1, TRUE>>}}
Assertion16 == iseq1({TRUE}) = {{<<1, TRUE>>}}
Assertion17 == RelITotalFunc({1}, {TRUE}) = {{<<1, TRUE>>}}
====