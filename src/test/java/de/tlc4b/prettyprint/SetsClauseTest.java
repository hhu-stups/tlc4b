package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.*;

import org.junit.Test;

public class SetsClauseTest {
	@Test
	public void testDeferredSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS d \n"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "CONSTANTS d\n"
				+ "====";
		String expectedConfig = "CONSTANTS\n" +
				"d = {d1,d2,d3}\n";

		compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testDeferredSet2() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS d \n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k : d \n"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "CONSTANTS d\n"
				+ "VARIABLES k\n"
				+ "Init == k \\in d\n"
				+ "\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<k>>\n"
				+ "====";
		String expectedConfig = "INIT Init\n"
				+ "NEXT Next\n"
				+ "CONSTANTS\n"
				+ "d = {d1,d2,d3}\n";

		compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testEnumeratedSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "SETS S = {a,b,c} \n"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "CONSTANTS a, b, c\n"
				+ "S == {a, b, c}\n"
				+ "====";
		String expectedConfig = "CONSTANTS\na = a\nb = b\nc = c\n"; 
		compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
}
