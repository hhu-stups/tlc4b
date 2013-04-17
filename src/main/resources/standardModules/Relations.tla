---- MODULE Relations -----
(* This module contains relational operator as well as functional operators,
 because in B function are relations and in some cases in TLA+ it is more effective
 to define a relation as a function *) 

EXTENDS TLC, Sequences, FiniteSets, Integers


				(* function operator *)
				
Range(f) == {f[x] : x \in DOMAIN f} (* Calculates the range of a function *)

(* injective total function *)
ITotalFunc(S,S2) == {f \in [S -> S2]: 
    Cardinality(DOMAIN f) = Cardinality(Range(f))}

(* partial function *)
PartialFunction(S, S2) ==  UNION{[x -> S2] :x \in SUBSET S} 

(* injective total function *)
IParFunc(S, S2)== {f \in PartialFunction(S, S2): Cardinality(DOMAIN f) = Cardinality(Range(f))}



(*Set of Relations*)
Relations(x,y) == SUBSET (x \times y)

(* Domain *)
RelDomain(r) == {x[1]: x \in r}

RelRange(r) == {x[2]: x \in r}

(* Identity relation *)
RelId(S) == {<<x,x>>: x \in S}

(* Functional call on a relation *)
RelCall(r, x) == (CHOOSE y \in r: y[1] = x)[2]

(* Domain restriction of a relation *)
RelDomRes(S, r) == {x \in r: x[1] \in S} 

(* Domain substraction of a relation *)
RelDomSub(S, r) == {x \in r: x[1] \notin S} 

(* Range restriction *)
RelRanRes(S, r) == {x \in r: x[2] \in S} 

(* Range substraction *)
RelRanSub(S, r) == {x \in r: x[2] \notin S} 

(* Inverse of relation *)
RelInverse(r) == {<<x[2],x[1]>>: x \in r} 

(* Relational image *)
RelImage(r, S) =={y[2] :y \in {x \in r: x[1] \in S}} 

(* Relational overriding *)
RelOver(r, r2) == {x \in r: x[1] \notin RelDomain(r2)} \cup r2 

(* Direct product *)
RelDirectProduct(r1, r2) == {<<x, u>> \in (RelDomain(r1) \cup RelDomain(r2)) \times (RelRange(r1) \times RelRange(r2)): 
	/\ u[1] \in RelImage(r1, {x}) 
	/\ u[2] \in RelImage(r2,{x})}

RelDirectProduct2(r1, r2) == {<<x, u>> \in (RelDomain(r1) \cup RelDomain(r2)) \times (RelRange(r1) \times RelRange(r2)): 
	/\ <<u[1],u[2][1]>> \in r1 
	/\ <<u[1],u[2][2]>> \in r2} 

RelComposition(r1, r2) == {<<u[1][1],u[2][2]>> : u \in 
		{x \in RelRanRes(RelDomain(r2),r1) \times RelDomRes(RelRange(r1) ,r2): x[1][2] = x[2][1]}} 

Prj1(E, F) == {u \in E \times F \times E: u[1] = u[3]}

Prj2(E, F) == {u \in E \times F \times F: u[2] = u[3]} 

RECURSIVE iterate(_,_) 
iterate(r, n) == CASE  n = 0 -> RelId(RelDomain(r) \cup RelRange(r)) 
		[] n = 1 -> r 
		[] OTHER -> iterate(RelComposition(r,r), n-1) 

RECURSIVE Closure1(_) 
Closure1(R) == IF RelComposition(R,R) \R # {} 
		THEN R \cup Closure1(RelComposition(R,R)) 
		ELSE R 

Closure(R) == Closure1( R \cup {<<x[1],x[1]>>: x \in R} \cup {<<x[2],x[2]>>: x \in R}) 

is_partial_func(f) == \A x \in RelDomain(f): Cardinality(RelImage(f, {x})) =< 1 

is_partial_func2(f, S, S2) == /\ \A x \in f: x[1] \in S /\ x[2] \in S2 /\ RelImage(f, {x[1]}) = {x[2]} 

is_func(f) == \A x \in RelDomain(f): Cardinality(RelImage(f, {x})) < 2 

(* convert a function to a relation*)
MakeRel(f) == {<<x, f[x]>>: x \in DOMAIN f} 

(* test if a relation f is a total function *)
RelIsTotalFunc(f, S, S2) == 
    /\RelDomain(f) = S 
    /\ \A x \in f: /\ x[1] \in S 
        /\ x[2] \in S2 
        /\ RelImage(f, {x[1]}) = {x[2]} 


RelTotalFunc(S, S2) == {MakeRel(f): f \in [S -> S2]}

RelITotalFunc(S, S2) == {MakeRel(f): f \in ITotalFunc(S, S2)} 

RelParFunc2(S, S2) == {MakeRel(f):  f \in UNION{[x -> S2] :x \in SUBSET S}}
RelParFunc(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x)} 

RelIParFunc(S, S2) == {MakeRel(f): f \in IParFunc(S, S2)}


is_injectiv_func(f) == \A x \in RelRange(f): Cardinality(RelImage(RelInverse(f), {x})) =< 1 
 


total_surjection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x)/\ RelDomain(x)= S /\ S2 = RelRange(x)} 

partial_surjection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x)/\ S2 = Range(x)} 

total_bijection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ RelDomain(x) = S /\ is_injectiv_func(x) /\ S2 = RelRange(x)} 

MakeRelations(S) == {MakeRel(f): f \in S}

(* Sequences *)
ISeq(S) ==  UNION {ITotalFunc(1..n,S) :n \in 0..Cardinality(S)} 

ISeq1(S) == ISeq(S) \ {<<>>} 

Concat(s, s2) == {<<i, IF i \leq Cardinality(s) THEN RelCall(s, i) ELSE RelCall(s2, i-Cardinality(s))>> : i \in 1.. (Cardinality(s) + Cardinality(s2))}
    
RelISeq(S) == MakeRelations(ISeq(S))    

RelISeq1(S) == MakeRelations(ISeq1(S))

iseq(S) == {x \in SUBSET {<<x,y>> \in (1 .. Cardinality(S)) \times S : TRUE }: 
    /\ Cardinality(x) =< Cardinality(S)
 /\ \E z \in 0.. Cardinality(S): RelDomain(x) = 1..z
 /\ is_func(x)
 /\ is_injectiv_func(x)} 
iseq1(S) == iseq(S) \ {{}} 
 
total_func(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ RelDomain(x)= S} 

test(S, S2) == {x \in (SUBSET (S \times S2)): RelDomain(x)= S /\ Cardinality(x) = Cardinality(RelDomain(x))} 
    
============






