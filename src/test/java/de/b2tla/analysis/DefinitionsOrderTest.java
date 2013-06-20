package de.b2tla.analysis;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

public class DefinitionsOrderTest {

	
	@Test
	public void testDefinitionsInOrder() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS def1 == 1;\n"
				+ "def2 == def1 \n"
				+ "PROPERTIES def2 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "def1 == 1\n"
				+ "def2 == def1 \n"
				+ "ASSUME def2 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testDefinitionsReverserOrder() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS def1 == def2;\n"
				+ "def2 == 1 \n"
				+ "PROPERTIES def1 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "def2 == 1\n"
				+ "def1 == def2 \n"
				+ "ASSUME def1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testConstantsDependsOnBDefinitions() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS def == 1;\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = def \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "def == 1\n"
				+ "k == def \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testBDefinitionDependsOnConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS def == k = 1;\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & def\n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "k == 1\n"
				+ "def == k = 1 \n"
				+ "ASSUME def \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testDefinitionDependsOnConstantAndViceVersa() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS def == k2 + 1 ;\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = def & k2 = 1\n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "k2 == 1\n"
				+ "def == k2 + 1 \n"
				+ "k == def \n"
				+ "======";
		compare(expected, machine);
	}
	
	
}
