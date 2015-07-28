package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class SetComprehensionOptimizerTest {

	@Test
	public void testSetComprehension1() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x,y | x : 1..10 & y = x + 1} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "k == {<<x, x + 1>>: x \\in {x \\in ((1 .. 10)): TRUE}} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension2() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x,y|  x : 1..10 & x = y & y = x} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "k == {<<x, x + 1>>: x \\in {x \\in ((1 .. 10)): TRUE}} \n"
				+ "======";
		compare(expected, machine);
	}
}
