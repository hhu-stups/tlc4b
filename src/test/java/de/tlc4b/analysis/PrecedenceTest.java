package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.compare;

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
	public void testMult() throws Exception {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 * 2 * 3 = 6 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME 1 * 2 * 3 = 6\n"
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
