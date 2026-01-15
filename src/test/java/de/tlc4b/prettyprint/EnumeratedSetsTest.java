package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class EnumeratedSetsTest {
	@Test
	public void testTwoEnumeratedSets() throws Exception {
		String machine = "MACHINE test\n" 
				+ "SETS set = {a,b,c}; set2 = {d}\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "CONSTANTS a, b, c, d\n"
				+ "set == {a, b, c}\n" 
				+ "set2 == {d}\n" 
				+ "====";
		final String config = "CONSTANTS\na = a\nb = b\nc = c\nd = d\n";
		TestUtil.compareModuleAndConfig(expected, config, machine);
	}
}
