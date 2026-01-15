package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class LogicalPredicatesTest {

	@Test
	public void testEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testConvert() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES TRUE = bool(1=1)" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME TRUE = (1=1) \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testNotEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 /= 1" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME 1 # 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testImplication() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 => 1 = 1 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "ASSUME  1 = 1 => 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}

	@Test
	public void testMembershipIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 0 : (INTEGER /\\ {0}) \n"
				+ "END";

		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers \n"
				+ "ASSUME 0 \\in Int \\cap {0} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
}
