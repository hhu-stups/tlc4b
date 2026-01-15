package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class ClausesTest {

	
	@Test
	public void testAssertion() throws Exception {
		String machine = "MACHINE test\n"
				+ "ASSERTIONS 1 = 1\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME Assertion1 == 1 = 1\n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testAssertion2() throws Exception {
		String machine = "MACHINE test\n"
				+ "ASSERTIONS 1 = 1; 2 = 2\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME Assertion1 == 1 = 1\n"
				+ "ASSUME Assertion2 == 2 = 2\n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testAbstractConstants() throws Exception {
		String machine = "MACHINE test\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k = 1\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "k == 1 "
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testConcreteConstants() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONCRETE_CONSTANTS k\n"
				+ "PROPERTIES k = 1\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "k == 1 "
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
}
