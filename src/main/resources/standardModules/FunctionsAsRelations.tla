------------------------ MODULE FunctionsAsRelations ----------------------------------
EXTENDS FiniteSets, Functions, TLC, Sequences

LOCAL RelDom(r) == { x[1] :x \in r} 
LOCAL RelRan(r) == { x[2] :x \in r} 

RelCall(r, x) == 
    IF Assert(Cardinality(r) = Cardinality(RelDom(r)), "Applied a function call to the relation: " \o ToString(r))
    THEN (CHOOSE y \in r: y[1] = x)[2]
    ELSE FALSE
                 
LOCAL MakeRel(f) == {<<x, f[x]>>: x \in DOMAIN f}    
LOCAL Rel(S, S2) == SUBSET (S \times S2)    
LOCAL func(f) == Cardinality(RelDom(f)) = Cardinality(f)
LOCAL total(f, dom) == RelDom(f) = dom
LOCAL inj(f) == Cardinality(RelRan(f)) = Cardinality(f)
LOCAL surj(f, ran) == RelRan(f) = ran

RelTotalFunc(S, S2) == {MakeRel(f): f \in [S -> S2]}
RelTotalFuncEleOf(S, S2) == {f \in Rel(S,S2): func(f) /\ total(f,S)}

RelTotalInjFunc(S, S2) == {MakeRel(f): f \in TotalInjFunc(S, S2)} 
RelTotalInjFuncEleOf(S, S2) == {f \in Rel(S,S2): func(f) /\ total(f,S) /\ inj(f)}

RelTotalSurFunc(S, S2) == {MakeRel(f): f \in TotalSurFunc(S, S2)} 
RelTotalSurFuncEleOf(S, S2) == {f \in Rel(S,S2): 
    /\ func(f) /\ total(f,S) /\ surj(f, S2)}

RelTotalBijFunc(S, S2) == {MakeRel(f): f \in TotalBijFunc(S, S2)} 
RelTotalBijFuncEleOf(S, S2) == {f \in (SUBSET (S \times S2)):
    /\ func(f) /\ total(f,S) /\ inj(f) /\ surj(f, S2)}

RelParFunc(S, S2) == {MakeRel(f):  f \in ParFunc(S, S2)}
RelParFuncEleOf(S, S2) == {f \in Rel(S, S2): func(f)} 

RelParInjFunc(S, S2) == {MakeRel(f):  f \in ParInjFunc(S, S2)}
RelParInjFuncEleOf(S, S2) == {f \in Rel(S, S2): func(f) /\ inj(f)} 

RelParSurFunc(S, S2) == {MakeRel(f):  f \in ParSurFunc(S, S2)}
RelParSurFuncEleOf(S, S2) == {f \in Rel(S, S2): func(f) /\ surj(f, S2)}

RelParBijFunc(S, S2) == {MakeRel(f):  f \in ParBijFunc(S, S2)}
RelParBijFuncEleOf(S, S2) == {f \in Rel(S, S2): func(f) /\ surj(f, S2) /\ inj(f)}                 
=========================================================================================