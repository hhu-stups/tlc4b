package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

import de.tlc4b.exceptions.SubstitutionException;

public class SubstitutionsTest {
	
	
	@Test (expected = SubstitutionException.class)
	public void testVariableAssignedTwice() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x\n"
				+ "INVARIANT x = 1 \n" + "INITIALISATION x := 1 || x := 1 \n"
				+ "END";
		compare(null, machine);
	}
	
	@Test  (expected = SubstitutionException.class)
	public void testMissingVariableAssignment() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y \n"
				+ "INVARIANT x = 1 & y = 1 \n" + "INITIALISATION x := 1 \n"
				+ "END";
		compare(null, machine);
	}
	
	@Test
	public void testLet() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION LET a,b BE a = 1 & b = 2 IN x := a +b END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Inv == x = 1\n"
				+ "Init == \\E a \\in {1}, b \\in {2} : TRUE /\\ x = a + b \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testAny() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION ANY a,b WHERE a = 1 & b = 2 THEN x := a +b END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == \\E a \\in {1}, b \\in {2} : x = a + b \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testPre() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION PRE 1 = 1 THEN x := 1 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == \n/\\ 1 = 1 \n/\\ x = 1\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testAssert() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION ASSERT 1 = 1 THEN x := 1 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == \n/\\1 = 1 \n/\\ x = 1\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testNotDeterministicElementOf() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x :: {1} \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x \\in {1}\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testIFElseIFSubstitution() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION IF 1=1 THEN x:= 1 ELSIF 1=2 THEN x:= 2 ELSE x:= 4 END \n"
				+ "END";
		
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == (CASE 1 = 1 -> x = 1 [] 1 = 2 -> x = 2 [] OTHER -> x = 4)\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
}
