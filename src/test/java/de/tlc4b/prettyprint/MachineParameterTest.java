package de.tlc4b.prettyprint;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class MachineParameterTest {

	@Test
	public void testScalarParameterToConstant() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a = 1\n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testScalarParameterToVariable() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a : {1,2,3}\n"
				+ "END";
		
		String expectedModule = "---- MODULE test ----\n"
				+ "VARIABLES a\n"
				+ "Init == a \\in {1, 2, 3}\n"
				+ "\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<a>>\n"
				+ "====";
		String expectedConfig = "INIT Init\nNEXT Next\n";
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
	@Test
	public void testTwoScalarParameter() throws Exception {
		String machine = "MACHINE test(a,b)\n"
				+ "CONSTRAINTS a = 1 & b = 2 \n"
				+ "END";
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "b == 2 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testParameter() throws Exception {
		String machine = "MACHINE test(AA)\n"
				+ "END";
		
		String expectedModule = "---- MODULE test ----\n"
				+ "CONSTANTS AA\n"
				+ "====";
		String expectedConfig = "CONSTANTS\nAA = {AA1,AA2,AA3}\n";
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
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
				+ "ASSUME Cardinality(B) = 2\n"
				+ "====";
		String expectedConfig = "CONSTANTS\nB = {B1,B2,B3}\n";
		TestUtil.compareModuleAndConfig(expectedModule, expectedConfig, machine);
	}
	
}
