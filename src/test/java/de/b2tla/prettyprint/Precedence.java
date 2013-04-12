package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class Precedence {

	
	@Test
	public void testGreaterThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES TRUE = bool(2 > 1)\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME TRUE = (2 > 1)\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNatural1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} =  NATURAL - NATURAL1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME {1} = Nat \\ (Nat \\ {0})\n"
				+ "======";
		compare(expected, machine);
	}
}
