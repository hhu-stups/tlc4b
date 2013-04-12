package de.b2tla;

public class StandardModules {

	public final static String BBuiltIns = "---- MODULE BBuiltIns ----\n"
			+ "EXTENDS Integers, FiniteSets \n"
			+ "RECURSIVE SIGMA(_) \n" 
			+ "SIGMA(S) == "
				+ "LET e == CHOOSE e \\in S: TRUE"
				+ " IN IF  S = {} THEN 0 ELSE e + SIGMA(S \\ {e}) \n" 
			+ "succ[x \\in Int] == x + 1 \n "
			+ "pred[x \\in Int] == x - 1 \n"
			+ "POW1(S) == (SUBSET S) \\ {{}} \n"
			+ "FIN(S) == {x \\in SUBSET S: IsFiniteSet(x)} \n"
			+ "FIN1(S) == {x \\in SUBSET S: IsFiniteSet(x) /\\ x # {}}"
			+ "a \\subset b == a \\subseteq b /\\ a # b \n"
			+ "notSubset(a, b) == ~ (a \\subseteq b) \n"
			+ "notStrictSubset(a, b) == ~ (a \\subset b ) \n"
			+ "RECURSIVE INTER(_) \n"
			+ "INTER(S) == "
				+ "LET e == (CHOOSE e \\in S: TRUE) \n"
				+ " IN IF  Cardinality(S) = 1 THEN e ELSE e \\cap INTER(S \\ {e}) \n" 
			+ "=========";
			
	public final static String Relations = "---- MODULE Relations -----\n"
			+ "EXTENDS TLC, Sequences, FiniteSets, Integers \n"
			+ "domain(r) == {x[1]: x \\in r}\n"
			+ "range(r) == {x[2]: x \\in r} \n"
			+ "id(S) == {<<x,x>>: x \\in S}\n"
			+ "set_of_relations(x,y) == SUBSET (x \\times y)\n"
			+ "domain_restriction(S, r) == {x \\in r: x[1] \\in S} \n"
			+ "domain_substraction(S, r) == {x \\in r: x[1] \\notin S} \n"
			+ "range_restriction(S, r) == {x \\in r: x[2] \\in S} \n"
			+ "range_substraction(S, r) == {x \\in r: x[2] \\notin S} \n"
			+ "rel_inverse(r) == {<<x[2],x[1]>>: x \\in r} \n"
			+ "relational_image(r, S) =={y[2] :y \\in {x \\in r: x[1] \\in S}} \n"
			+ "relational_overriding(r, r2) == {x \\in r: x[1] \\notin domain(r2)} \\cup r2 \n"
			+ "relational_overriding2(r, p, v) == {x \\in r: x[1] # p} \\cup {<<p, v>>} \n"
			+ "direct_product(r1, r2) == {<<x, u>> \\in (domain(r1) \\cup domain(r2)) \\times (range(r1) \\times range(r2)): \n"
			+ "		u[1] \\in relational_image(r1, {x}) /\\ u[2] \\in relational_image(r2,{x})}"
			+ "direct_product2(r1, r2) == {u \\in (domain(r1) \\cup domain(r2)) \\times (range(r1) \\times range(r2)):"
			+ "     <<u[1],u[2][1]>> \\in r1 /\\ <<u[1],u[2][2]>> \\in r2} \n"
			+ "relational_composition(r1, r2) == {<<u[1][1],u[2][2]>> : u \\in \n"
			+ "		{x \\in range_restriction(domain(r2),r1) \\times domain_restriction(range(r1) ,r2): x[1][2] = x[2][1]}} \n"
			+ "prj1(E, F) == {u \\in E \\times F \\times E: u[1] = u[3]} \n"
			+ "prj2(E, F) == {u \\in E \\times F \\times F: u[2] = u[3]} \n"
			+ "RECURSIVE iterate(_,_) \n"
			+ "iterate(r, n) == CASE  n = 0 -> id(domain(r) \\cup range(r)) \n"
			+ "		[] n = 1 -> r \n"
			+ "		[] OTHER -> iterate(relational_composition(r,r), n-1) \n"
			+ "RECURSIVE closure1(_) \n"
			+ "closure1(R) == IF relational_composition(R,R) \\R # {} \n"
			+ "		THEN R \\cup closure1(relational_composition(R,R)) \n" 
			+ "		ELSE R \n"
			+ "closure(R) == closure1( R \\cup {<<x[1],x[1]>>: x \\in R} \\cup {<<x[2],x[2]>>: x \\in R}) \n"
			+ "relational_call(r, x) == (CHOOSE y \\in r: y[1] = x)[2] \n"

			
			
			+ "is_partial_func(f) == \\A x \\in domain(f): Cardinality(relational_image(f, {x})) =< 1 \n"
			+ "is_partial_func2(f, S, S2) == /\\ \\A x \\in f: x[1] \\in S /\\ x[2] \\in S2 /\\  relational_image(f, {x[1]}) = {x[2]} \n"

			
			+ "func_ran(f) == {f[x] : x \\in DOMAIN f} \n"
			+ "make_rel(f) == {<<x, f[x]>>: x \\in DOMAIN f} \n"
			
			//total
			//func
			+ "i_total_func(S,S2) == {f \\in [S -> S2]: Cardinality(DOMAIN f) = Cardinality(func_ran(f))} \n"
			//rel
			+ "total_func_rel(S, S2) == make_rel([S -> S2]) \n"
			+ "i_total_func_rel(S, S2) == make_rel(i_total_func(S, S2)) \n"
			
			
			//partial function
			+ "partial_func(S, S2) ==  UNION{[x -> S2] :x \\in SUBSET S} \n"
			+ "partial_func_rel(S, S2) == {make_rel(f):  f \\in UNION{[x -> S2] :x \\in SUBSET S}}\n"
			+ "i_partial_func(S, S2)== {f \\in partial_func(S, S2): Cardinality(DOMAIN f) = Cardinality(func_ran(f))}"
			
			+ "is_func(f) == \\A x \\in domain(f): Cardinality(relational_image(f, {x})) < 2 \n"
			+ "total_func(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x) /\\ domain(x)= S} \n"

			+ "is_total_func(f, S, S2) == domain(f) = S /\\ \\A x \\in f: x[1] \\in S /\\ x[2] \\in S2 /\\  relational_image(f, {x[1]}) = {x[2]} \n"

			+ "is_injectiv_func(f) == \\A x \\in range(f): Cardinality(relational_image(rel_inverse(f), {x})) =< 1 \n"
			+ "total_injection(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x) /\\ domain(x)= S /\\ is_injectiv_func(x) } \n"
			+ "partial_injection(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x) /\\ is_injectiv_func(x) } \n"

			+ "total_surjection(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x)/\\ domain(x)= S /\\ S2 = range(x)} \n"
			+ "partial_surjection(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x)/\\ S2 = range(x)} \n"

			+ "total_bijection(S, S2) == {x \\in (SUBSET (S \\times S2)): is_func(x) /\\ domain(x) = S /\\ is_injectiv_func(x) /\\ S2 = range(x)} \n"
			
			+ "iseq(S) == {x \\in SUBSET {<<x,y>> \\in (1 .. Cardinality(S)) \\times S : TRUE }: \n" 
            + "	/\\ Cardinality(x) =< Cardinality(S)\n"
            + " /\\ \\E z \\in 0.. Cardinality(S): domain(x) = 1..z\n"
            + " /\\ is_func(x)\n"
            + " /\\ is_injectiv_func(x)} \n"
			+ "iseq1(S) == iseq(S) \\ {{}} \n"
            + "concat(s, s2) == {<<i, IF i \\leq Cardinality(s) THEN relational_call(s, i) ELSE relational_call(s2, i-Cardinality(s))>>: i \\in 1.. (Cardinality(s) + Cardinality(s2))} \n"
            + "============";
	
}
