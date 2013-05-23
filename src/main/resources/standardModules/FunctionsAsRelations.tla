------------------------ MODULE FunctionsAsRelations ----------------------------------
EXTENDS FiniteSets, Relations, Functions

RelCall(r, x) == 
    IF Assert(Cardinality(r) = Cardinality(RelDomain(r)), "ERROR")
    THEN (CHOOSE y \in r: y[1] = x)[2]
    ELSE FALSE
                 
MakeRel(f) == {<<x, f[x]>>: x \in DOMAIN f}    
Rel(S, S2) == SUBSET (S \times S2)    
func(f) == Cardinality(RelDomain(f)) = Cardinality(f)
total(f, dom) == RelDomain(f) = dom
inj(f) == Cardinality(RelRange(f)) = Cardinality(f)
surj(f, ran) == RelRange(f) = ran

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