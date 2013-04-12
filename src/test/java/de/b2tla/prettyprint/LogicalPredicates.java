package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class LogicalPredicates {

	@Test
	public void testEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME 1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNotEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 /= 1" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME 1 # 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testImplication() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 => 1 = 1 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "ASSUME  1 = 1 => 1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
}
