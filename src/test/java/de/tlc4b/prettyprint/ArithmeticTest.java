package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

/**
 * Test of arithmetic operators.
 * Modulo and Division are not tested here because their translation is defined in the module BBuiltins
 * and they are only tested via integration tests.
 */
public class ArithmeticTest {

	@Test
	public void testInteger() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES INTEGER = INTEGER\n"
				+ "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME Int = Int\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testNatural() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES NATURAL = NATURAL\n"
				+ "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME Nat = Nat\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testNatural1() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES NATURAL1 = NATURAL1\n"
				+ "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME Nat \\ {0} = Nat \\ {0}\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testInt() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES INT = INT\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME (-1..3) = (-1..3)\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testNat() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES NAT = NAT\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME (0..3) = (0..3)\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testNat1() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES NAT1 = NAT1\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME (1..3) = (1..3)\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testInterval() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES {1,2,3} = 1..3\n"
				+ "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME {1,2,3} = 1..3\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testGreaterThan() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 2 > 1\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME 2 > 1\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testLessThan() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 1 < 2\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME 1 < 2\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testGreaterThanEquals() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 1 >= 2\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME 1 >= 2\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testLessThanEquals() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 1 <= 2\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "ASSUME 1 =< 2\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testAdd() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 2 = 1 + 1\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals \n"
				+ "ASSUME 2 = 1 + 1 \n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testMinus() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 1 = 2 - 1\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals \n"
				+ "ASSUME 1 = 2 - 1 \n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testMult() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES 1 = 1 * 1\n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 * 1 \n" + "======";
		TestUtil.compare(expected, machine);
	}


	@Test
	public void testUnaryMinus() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES -1 = 1  \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME -1 = 1\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testMinInt() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES MININT = MININT  \n"
				+ "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME -1 = -1\n" + "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testMaxInt() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES MAXINT = MAXINT  \n"
				+ "END";
		String expected = "---- MODULE test----\n" + "ASSUME 3 = 3\n"
				+ "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testSetComprehensionInt() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x| 1=1 => x = 1} = {} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {x \\in (Int): 1 = 1 => x = 1} = {}\n" + "======";
		TestUtil.compare(expected, machine);
	}

}
