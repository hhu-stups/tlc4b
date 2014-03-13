package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class ConstantsEvaluatorTest {

	
	@Test
	public void testConstants() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = k2 & k2 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "k2 == 1 \n"
				+ "k == k2 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testConstants2() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "PROPERTIES k = k2 + 1 & k2 = k3 & k3 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "k3 == 1 \n"
				+ "k2 == k3 \n"
				+ "k == k2 + 1 \n"
				+ "======";
		compare(expected, machine);
	}
}
