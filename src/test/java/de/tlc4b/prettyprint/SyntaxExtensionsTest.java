package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class SyntaxExtensionsTest {

	@Test
	public void testIfThenElseg() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 =  (IF 1=1 THEN 1 ELSE 2 END)  \n" + "END";
		
		String expected = "---- MODULE test----\n" 
				+ "ASSUME 1 = (IF 1 = 1 THEN 1 ELSE 2) \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
}
