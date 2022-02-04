package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

public class StringTest {

	@Test
	public void testString() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES \"abc\" = \"abc\" " + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME \"abc\" = \"abc\" \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testString2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x: STRING)" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME \\E x \\in STRING : TRUE \n"
				+ "======";
		compare(expected, machine);
	}

}
