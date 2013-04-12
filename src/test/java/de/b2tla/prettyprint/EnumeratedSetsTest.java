package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;

import org.junit.Test;

public class EnumeratedSetsTest {
	@Test
	public void testSetComprehensionEquals() throws Exception {
		// TODO verify config
		String machine = "MACHINE test\n" + "SETS set = {a,b,c}; set2 = {d}\n"
				+ "END";

		String expected = "---- MODULE test ----\n" + "CONSTANTS a, b, c, d\n"
				+ "set == {a, b, c}\n" + "set2 == {d}\n" + "====";
		compareEquals(expected, machine);
	}
}
