package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

public class NumbersTest {

	
	@Test
	public void testInteger() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INTEGER = INTEGER\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME Int = Int\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNatural() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NATURAL = NATURAL\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat = Nat\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNatural1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NATURAL1 = NATURAL1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat \\ {0} = Nat \\ {0}\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testInt() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INT = INT\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME Int = Int\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNat() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NAT = NAT\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat = Nat\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNat1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NAT1 = NAT1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat \\ {0} = Nat \\ {0}\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testInterval() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2,3} = 1..3\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME {1,2,3} = 1..3\n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testGreaterThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 > 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 2 > 1\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testLessThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 < 2\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 < 2\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testGreaterThanEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 >= 2\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 >= 2\n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testLessThanEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 <= 2\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 =< 2\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testMin() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = min({1,2,3})\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = CHOOSE min \\in {1,2,3}: \\A p \\in {1,2,3}: min =< p \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testMax() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 3 = max({1,2,3})\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 3 = CHOOSE max \\in {1,2,3}: \\A p \\in {1,2,3}: max >= p \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testAdd() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 = 1 + 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 2 = 1 + 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testMinus() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 2 - 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 2 - 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testMult() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 * 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 * 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testDiv() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 / 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 \\div 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testPower() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 ** 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 ^ 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testModulo() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 0 = 1 mod 1\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 0 = 1 % 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testUnaryMinus() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES -1 = 1  \n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME -1 = 1\n"
				+ "======";
		compare(expected, machine);
	}
	
	
	
}
