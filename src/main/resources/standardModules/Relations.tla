---------------------------- MODULE Relations ----------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

Relation(X, Y) == SUBSET (X \times Y)
 (* The set of all relations with domain X and range Y. *)
 
RelDomain(R) == {x[1]: x \in R}
  \* The domain of the relation R.

RelRange(R) == {x[2]: x \in R}
 \* The range of the relation R.

RelId(S) == {<<x,x>>: x \in S}
 \* The identity relation of set S.

RelDomRes(S, R) == {x \in R: x[1] \in S} 
 \* The restriction on the domain of R for set S.
 
RelDomSub(S, R) == {x \in R: x[1] \notin S} 
 \* The subtraction on the domain of R for set S.

RelRanRes(R, S) == {x \in R: x[2] \in S} 
 \* The restriction on the range of R for set S.

RelRanSub(R, S) == {x \in R: x[2] \notin S}
 \* The subtraction on the range of R for set S.

RelInverse(R) == {<<x[2],x[1]>>: x \in R}
 \* The reverse relation of R.
 
RelImage(R, S) =={y[2] :y \in {x \in R: x[1] \in S}}
 \* The image of R for set S.
  
RelOverride(R1, R2) == {x \in R1: x[1] \notin RelDomain(R2)} \cup R2 
 \* Overwriting of relation r1 with r2.

RelComposition(r1, r2) == {<<u[1][1],u[2][2]>> : u \in 
    {x \in RelRanRes(r1, RelDomain(r2)) \times RelDomRes(RelRange(r1) ,r2):
        x[1][2] = x[2][1]}}
  \* The relational composition of r1 and r2.

RelDirectProduct(R1, R2) == {<<x, u>> \in RelDomain(R1) \times (RelRange(R1) \times RelRange(R2) ): 
    /\ <<x,u[1]>> \in R1 
    /\ <<x,u[2]>> \in R2}
 \* The direct product of relation R1 with R2.

RelParallelProduct(R1, R2) == {<<a, b>> \in (RelDomain(R1) \times RelDomain(R2)) 
                                            \times (RelRange(R1) \times RelRange(R2))
                              : <<a[1],b[1]>> \in R1 /\ <<a[2],b[2]>> \in R2 }
 \* The parallel product of R1 and R2.

RelPrj1(E, F) == {<<<<a,b>>, a>> : a  \in E, b \in F}
 \* The first projection relation.

RelPrj2(E, F) == {<<<<a,b>>, b>> : a  \in E, b \in F}
 \* The second projection relation.

RECURSIVE RelIterate(_,_) 
RelIterate(R, n) == CASE n < 0 -> Assert(FALSE, "")
        [] n = 0 -> RelId(RelDomain(R) \cup RelRange(R)) 
        [] n = 1 -> R 
        [] OTHER -> RelComposition(R,RelIterate(R, n-1)) 
  \* The relation of R iterated n times in relation to the composition operator
                                 
RelClosure1(R)  == \* Warshall algorithm from Leslie Lamport's Hyperbook
    LET NR == { r[1] : r \in R} \cup { r[2] : r \in R} 
        RECURSIVE W(_)
        W(L) == IF L = {}
                THEN R
                ELSE LET n == CHOOSE node \in L : TRUE
                        WM == W(L \ {n})
                     IN TLCEval(WM \cup {rs \in NR \times NR :
                            (<<rs[1],n>> \in WM) \land (<<n, rs[2]>> \in WM)})
    IN W(NR)
 \* The transitive closure of R.

RelClosure(R) == RelClosure1( R \cup {<<x[1],x[1]>>: x \in R} \cup RelIterate(R, 0)) 
 \* The transitive and reflexive closure of R

RelFnc(R) ==  {<<x, RelImage(R, {x})>> :x \in RelDomain(R)}
 \* The transformation of R into a function

RECURSIVE RelRel(_)
RelRel(Fct) == IF Fct = {}
             THEN {}
             ELSE LET e == CHOOSE x \in Fct: TRUE
                  IN {<<e[1], y>>: y \in e[2]} \cup RelRel(Fct\{e})
 \* The transformation of function Fct into a relation               
=============================================================================

