package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class PrecedenceTest {

	@Test
	public void testInterval() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k\n"
				+ "PROPERTIES k = (1..3) * (1..3) \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "k == (1 .. 3) \\times (1 .. 3)\n"
				+ "ASSUME k = (1 .. 3) \\times (1 .. 3)\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testPlusMinus() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 - 2 + 3 = 0 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 - 2 + 3 = 0 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testPlusMinus2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 - (2 + 1) = -2 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME 1 - (2 + 1) = -2 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testAndOr() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 & 1 = 1 or 1 = 1 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME (1 = 1 /\\ 1 = 1) \\/ 1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
}
