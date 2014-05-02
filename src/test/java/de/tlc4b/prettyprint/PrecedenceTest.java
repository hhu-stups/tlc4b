package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class PrecedenceTest {

	@Test
	public void testSubsetVsTimes() throws Exception {
		
		String machine = "MACHINE test\n"
				+ "PROPERTIES POW({1}) * {1} = POW({1}) * {1} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME (SUBSET{1}) \\times {1} = (SUBSET{1}) \\times {1}\n"
				+ "======";
		compare(expected, machine);
	}
}
