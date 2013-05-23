---------------------------- MODULE Relations ----------------------------
EXTENDS FiniteSets, Naturals, TLC

Relation(x,y) == SUBSET (x \times y) (*Set of Relations*)

RelDomain(r) == {x[1]: x \in r}

RelRange(r) == {x[2]: x \in r}

RelId(S) == {<<x,x>>: x \in S}

RelDomRes(S, r) == {x \in r: x[1] \in S} 

RelDomSub(S, r) == {x \in r: x[1] \notin S} 

RelRanRes(r, S) == {x \in r: x[2] \in S} 

RelRanSub(r, S) == {x \in r: x[2] \notin S}

RelInverse(r) == {<<x[2],x[1]>>: x \in r}

RelImage(r, S) =={y[2] :y \in {x \in r: x[1] \in S}}

RelOverride(r, r2) == {x \in r: x[1] \notin RelDomain(r2)} \cup r2 

RelDirectProduct(r1, r2) == {<<x, u>> \in RelDomain(r1) \times (RelRange(r1) \times RelRange(r2) ): 
    /\ <<x,u[1]>> \in r1 
    /\ <<x,u[2]>> \in r2}

RelComposition(r1, r2) == {<<u[1][1],u[2][2]>> : u \in 
    {x \in RelRanRes(r1, RelDomain(r2)) \times RelDomRes(RelRange(r1) ,r2):
        x[1][2] = x[2][1]}}

RelParallelProduct(r1, r2) == {<<a, b>> \in (RelDomain(r1) \times RelDomain(r2)) 
                                            \times (RelRange(r1) \times RelRange(r2))
                              : <<a[1],b[1]>> \in r1 /\ <<a[2],b[2]>> \in r2 }

RelPrj1(E, F) == {<<<<a,b>>, a>> : a  \in E, b \in F}

RelPrj2(E, F) == {<<<<a,b>>, b>> : a  \in E, b \in F}

RECURSIVE RelIterate(_,_) 
RelIterate(r, n) == CASE n < 0 -> Assert(FALSE, "ERROR")
        [] n = 0 -> RelId(RelDomain(r) \cup RelRange(r)) 
        [] n = 1 -> r 
        [] OTHER -> RelIterate(RelComposition(r,r), n-1) 

RECURSIVE RelClosure1(_) 
RelClosure1(R) == IF RelComposition(R,R) \ R # {} 
               THEN R \cup RelClosure1(RelComposition(R,R)) 
               ELSE R 

RelClosure(r) == RelClosure1( r \cup {<<x[1],x[1]>>: x \in r} \cup RelIterate(r, 0)) 

RelFnc(r) ==  {<<x, RelImage(r, {x})>> :x \in RelDomain(r)}

RECURSIVE RelRel(_)
RelRel(r) == IF r = {}
             THEN {}
             ELSE LET e == CHOOSE x \in r: TRUE
                  IN {<<e[1], y>>: y \in e[2]} \cup RelRel(r\{e})               
=============================================================================

