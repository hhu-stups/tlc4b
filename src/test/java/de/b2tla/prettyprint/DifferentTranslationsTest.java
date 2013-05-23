package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compareEquals;

import org.junit.Test;

public class DifferentTranslationsTest {

	@Test
	public void testTotalFunctionElementOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {(1,1)} : {1} --> {1}\n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS FunctionsAsRelations\n"
				+ "ASSUME {<<1, 1>>} \\in RelTotalFuncEleOf({1}, {1})\n"
				+ "====";
		compareEquals(expected, machine);
	}
	
	
	@Test
	public void testTotalFunction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {{(1,1)}} = {1} --> {1}\n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS FunctionsAsRelations\n"
				+ "ASSUME {{<<1, 1>>}} = RelTotalFunc({1}, {1})\n"
				+ "====";
		compareEquals(expected, machine);
	}
}
