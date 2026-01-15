package de.tlc4b.typechecking;

import de.be4.classicalb.core.parser.exceptions.BException;
import de.tlc4b.exceptions.TypeErrorException;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ArithmeticOperatorTest {

	@Test
	public void testInteger() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = INTEGER \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testIntegerException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = INTEGER \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testNatural() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = NATURAL \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testNaturalException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = NATURAL \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testNatural1() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = NATURAL1 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testNatural1Exception() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = NATURAL1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testInt() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = INT \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testIntException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = INT \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testNat() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = NAT \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testNatException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = NAT \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testNat1() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = NAT1 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testNat1Exception() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = NAT1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testInterval() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1..3 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testIntervalException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = 1..3 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test(expected = TypeErrorException.class)
	public void testIntervalException2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = TRUE..3 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testMaxInt() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = MAXINT \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testMaxIntException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES {} = MAXINT \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testMinInt() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = MININT \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testMinIntException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES {} = MININT \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testGreaterThan() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k > k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testGreaterThanException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE > 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testLessThan() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k < k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testLessThanException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE < 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testGreaterEquals() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k >= k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testGreaterEqualsException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE >= 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testLessEquals() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k <= k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testLessEqualsException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE <= 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testMin() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = min(k2) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testMinException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = min(k) \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testMax() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = max(k2) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testMaxException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = max(k) \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testAdd() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 + k3 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testAddException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = 1 + 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testDivision() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 / k3 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testDivisionException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = 1 / 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testPowerOf() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 ** k3 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testPowerOfException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = 1 ** 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testModulo() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 mod k3 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testModuloException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = 1 mod 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testSuccessor() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = succ \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSuccsessorException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE = succ \n"
				+ "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testPredecessor() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = pred \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testPredecessorException() throws BException {
		String machine = "MACHINE test\n" + "PROPERTIES TRUE = pred \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
}
