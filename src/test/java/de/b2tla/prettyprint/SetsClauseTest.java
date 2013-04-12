package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;

import org.junit.Test;

public class SetsClauseTest {
	@Test
	public void testDefferedSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS d \n"
				+ "END";
		String expectedModule = "---- MODULE test----\n"
				+ "CONSTANTS d\n"
				+ "======";
		String expectedConfig = "CONSTANTS\n" +
				"d = {d_1, d_2, d_3}\n";

		compareConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testEnumeratedSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS S = {a,b,c} \n"
				+ "END";
		String expectedModule = "---- MODULE test----\n"
				+ "CONSTANTS a, b, c\n"
				+ "S == {a, b, c}"
				+ "======";
		String expectedConfig = "CONSTANTS a = a\n b = b \n c = c"; 
		compareConfig(expectedModule, expectedConfig, machine);
	}
}
