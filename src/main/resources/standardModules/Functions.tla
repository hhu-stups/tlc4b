----------------------------- MODULE Functions -----------------------------
EXTENDS FiniteSets

Range(f) == {f[x] : x \in DOMAIN f}
 \* The range of the function f.
  
Image(f,S) == {f[x] : x \in S \cap DOMAIN f}
 \* The image of f for set S.
 
Id(S) == [x \in S|-> x]
 \* The identity function of set S.

DomRes(S, f) == [x \in (S \cap DOMAIN f) |-> f[x]] 
 \* The restriction on the domain of f for set S.

DomSub(S, f) == [x \in DOMAIN f \ S |-> f[x]] 
 \* The subtraction on the domain of f for set S.

RanRes(f, S) == [x \in {y \in DOMAIN f: f[y] \in S} |-> f[x]] 
 \* The restriction on the range of f for set S.
 
RanSub(f, S) == [x \in {y \in DOMAIN f: f[y] \notin S} |-> f[x]] 
 \* The subtraction on the range of f for set S.
 
Inverse(f) == {<<f[x],x>>: x \in DOMAIN f}
 \* The reverse relation of f.

Override(f, g) == [x \in (DOMAIN f) \cup DOMAIN g |-> IF x \in DOMAIN g THEN g[x] ELSE f[x]] 
 \* Overwriting of function f with g.
 
FuncAssign(f, d, e) == Override(f, [x \in {d} |-> e])
 \* Overwriting the function f at index d with value e.
 
TotalInjFunc(S, T) == {f \in [S -> T]: 
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all total injective functions whereby the domain is S and the range is a subset of T.

TotalSurFunc(S, T) == {f \in [S -> T]: T = Range(f)}
 \* The set of all total surjective functions whereby the domain is S and the range is T.

TotalBijFunc(S, T) == {f \in [S -> T]: T = Range(f) /\
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all total bijective functions whereby the domain is S and the range is T.
    
ParFunc(S, T) ==  UNION{[x -> T] :x \in SUBSET S}
 \* The set of all partial functions where the domain is a subset S and the range is a subset T.

isParFunc(f,S,T) == {x \in {f}:  DOMAIN x \subseteq S /\ Range(x) \subseteq T} 
 
isEleOfParFunc(f, S, T) == DOMAIN f \subseteq S /\ Range(f) \subseteq T 
 \* Test if the function f is a partial function
 
ParInjFunc(S, T)== {f \in ParFunc(S, T):
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
\* The set of all partial injective functions where the domain is a subset S and the range is a subset of T.

ParSurFunc(S, T)== {f \in ParFunc(S, T): T = Range(f)}
\* The set of all partial surjective functions where the domain is a subset S and the range is T.


ParBijFunc(S, T) == {f \in ParFunc(S, T): T = Range(f) /\
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all partial bijective functions where the domain is a subset S and the range is T.

    
=============================================================================
