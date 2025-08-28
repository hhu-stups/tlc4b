package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class FunctionsVsRelationsTest {

	@Test
	public void testCardOnAFunction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = card(%x.(x = 1 | 1))\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "EXTENDS FiniteSets\n"
				+ "ASSUME 1 = Cardinality(DOMAIN([x \\in {1} |-> 1 ]))\n"
				+ "======";
		compare(expected, machine);
	}
}
