package b2tla;

public class StandardModules {

	public final static String BBuiltIns = "---- BBuiltIns ----\n"
			+ "EXTENDS Integers, FiniteSets \n"
			+ "RECURSIVE SIGMA(_) \n" 
			+ "SIGMA(S) == "
				+ "LET e == CHOOSE e \\in S: TRUE"
				+ " IN IF  S = {} THEN 0 ELSE e + SIGMA(S \\ {e}) \n" 
			+ "succ[x \\in Int] == x + 1 \n "
			+ "pred[x \\in Int] == x - 1 \n"
			+ "POW1(S) == (SUBSET S) \\ {} \n"
			+ "FIN(S) == {x \\in S: IsFiniteSet(x)} \n"
			+ "FIN1(S) == {x \\in S: IsFiniteSet(x) /\\ x # {}}"
			+ "a \\subset b == a \\subseteq b /\\ a # b \n"
			+ "notSubset(a, b) == ~ (a \\subseteq b) \n"
			+ "notStrictSubset(a, b) == ~ (a \\subseteq b ) \n"
			+ "RECUSIVE union(_) \n"
			+ "inter(S) == "
				+ "LET e == CHOOSE e \\in S: TRUE"
				+ " IN IF  Cardinality(S) = 1 THEN e ELSE e \\cap inter(S \\ {e}) \n" 
			;
			
}
