----------------------------- MODULE Functions -----------------------------
EXTENDS FiniteSets

Range(f) == {f[x] : x \in DOMAIN f}

Image(f,S) == {f[x] : x \in S}

TotalInjFunc(S, S2) == {f \in [S -> S2]: 
    Cardinality(DOMAIN f) = Cardinality(Range(f))}

TotalSurFunc(S, S2) == {f \in [S -> S2]: S2 = Range(f)}

TotalBijFunc(S, S2) == {f \in [S -> S2]: S2 = Range(f) /\
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
    
ParFunc(S, S2) ==  UNION{[x -> S2] :x \in SUBSET S} 
isEleOfParFunc(f, S, S2) == DOMAIN f \subseteq S /\ Range(f) \subseteq S2 

ParInjFunc(S, S2)== {f \in ParFunc(S, S2):
    Cardinality(DOMAIN f) = Cardinality(Range(f))}

ParSurFunc(S, S2)== {f \in ParFunc(S, S2): S2 = Range(f)}

ParBijFunc(S, S2) == {f \in ParFunc(S, S2): S2 = Range(f) /\
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
=============================================================================
