package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;

import org.junit.Test;

public class MachineParameterTest {

	@Test
	public void testScalarParameterToConstant() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a = 1\n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "ASSUME a = 1\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testScalarParameterToVariable() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a : {1,2,3}\n"
				+ "END";
		
		String expectedModule = "---- MODULE test----\n" 
				+ "VARIABLES a\n"
				+ "Init == a \\in {1,2,3}\n"
				+ "======";
		String expectedConfig = "INIT Init";
		compareConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testTwoScalarParameter() throws Exception {
		String machine = "MACHINE test(a,b)\n"
				+ "CONSTRAINTS a = 1 & b = 2 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "b == 2 \n"
				+ "ASSUME a = 1 /\\ b = 2\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testParameter() throws Exception {
		String machine = "MACHINE test(AA)\n"
				+ "END";
		
		String expectedModule = "---- MODULE test----\n" 
				+ "CONSTANTS AA\n"
				+ "======";
		String expectedConfig = "CONSTANTS AA = {AA_1, AA_2, AA_3}";
		compareConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testMixedParameter() throws Exception {
		String machine = "MACHINE test(a, B)\n"
				+ "CONSTRAINTS a = 1 & card(B)= 2 \n"
				+ "END";
		String expectedModule = "---- MODULE test ----\n"
				+ "EXTENDS FiniteSets\n"
				+ "CONSTANTS B\n"
				+ "a == 1\n"
				+ "ASSUME a = 1 /\\ Cardinality(B) = 2\n"
				+ "====";
		String expectedConfig = "CONSTANTS B = {B_1, B_2, B_3}";
		compareConfig(expectedModule, expectedConfig, machine);
	}
	
}