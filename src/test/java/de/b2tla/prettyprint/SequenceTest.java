package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compareEquals;

import org.junit.Test;

public class SequenceTest {

	
	@Test
	public void testConcatination() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {(1,2)}^{(2,2)} = {(1,2),(1,3)} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS SequencesAsRelations\n"
				+ "ASSUME {<<1, 2>>} \\o {<<2, 2>>} = {<<1, 2>>, <<1, 3>>}\n"
				+ "====";
		compareEquals(expected, machine);
	}
}
