package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class ClausesTest {

	
	@Test //TODO include config
	public void testAssertion() throws Exception {
		String machine = "MACHINE test\n"
				+ "ASSERTIONS 1 = 1\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "Assertions == \\/ 1 = 1\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testAssertion2() throws Exception {
		String machine = "MACHINE test\n"
				+ "ASSERTIONS 1 = 1; 2 = 2\n"
				+ "END";
		String expected = "---- MODULE test ----\n"
				+ "Assertions == \\/ 1 = 1 \\/ 2 = 2\n"
				+ "======";
		compare(expected, machine);
	}
	
}
