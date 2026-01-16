package de.tlc4b.analysis;

import de.tlc4b.exceptions.NotSupportedException;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class ExpressionConstantTest {

	@Test
	public void testAConstantIsconstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & !x.(x = k => 1 = 1)\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME \\A x \\in {k} : 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testAConstantIsconstant2() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = k2 & k2 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k2 == 1 \n"
				+ "k == k2 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testBoundedVariable() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES !x.(x = 1 => !y.(y= x => 1 = 1))\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\A x \\in {1} : \\A y \\in {x} : 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test (expected = NotSupportedException.class)
	public void testNotConstantBoundedVariable() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES !x,y.(x = y & y = 1 => 1 = 1)\n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers \n"
				+ "ASSUME \\A x \\in Int, y \\in {1} : x = y => 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
}
