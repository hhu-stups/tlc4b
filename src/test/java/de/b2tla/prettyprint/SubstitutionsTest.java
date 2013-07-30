package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class SubstitutionsTest {
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
				+ "Init == \\E a \\in {1}, b \\in {2} : TRUE /\\ x = a + b \n"
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
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == 1 = 1 /\\ x = 1\n"
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
				+ "Invariant == x = 1\n"
				+ "Init == 1 = 1 /\\ x = 1\n"
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
}
