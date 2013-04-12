package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class DataTypesTest {

	@Test
	public void testString() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES \"abc\" = \"abc\" "
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME \"abc\" = \"abc\" \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testPair() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (3,4) = (3,4) \n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME <<3, 4>> = <<3, 4>> \n"
				+ "======";
		compare(expected, machine);
	}

	
	@Test
	public void testSequence() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES [3,4] = [3,4] \n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME <<3, 4>> = <<3, 4>> \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSequenceVsPair() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES [3,4] = {(3,4)} \n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME {<<1, 3>>, <<2, 4>>} = {<<3, 4>>} \n"
				+ "======";
		compare(expected, machine);
	}
	
}
