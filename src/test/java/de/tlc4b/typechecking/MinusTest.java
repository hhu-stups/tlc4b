package de.tlc4b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;



import de.be4.classicalb.core.parser.exceptions.BException;
import de.tlc4b.exceptions.TypeErrorException;

public class MinusTest {

	@Test
	public void testMinus() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = k2 - 1 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testMinus2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES 1 = k - k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testMinusException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES TRUE = 1 - 1 \n" + "END";
		new TestTypechecker(machine);
	}

	@Test
	public void testSetSubstraction() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES {1} = k - k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test
	public void testSetSubstraction2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = k2 - {1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSetSubstractionVsMinus() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1 - {1} \n" + "END";
		new TestTypechecker(machine);
	}

	@Test(expected = TypeErrorException.class)
	public void testSetSubstractionVsMinus2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = k - {1} \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testSetSubstraction3() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 - k3 & k3 = {1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k3").toString());
	}
	
	@Test
	public void testSetSubstraction4() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = k2 - k3 - {1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k3").toString());
	}
	
	@Test
	public void testSetSubstraction5() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2,k3,k4 \n"
				+ "PROPERTIES k - k2 - k3 = k4 - {1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k3").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k4").toString());
	}
	
}
