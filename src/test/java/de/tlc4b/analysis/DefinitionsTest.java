package de.tlc4b.analysis;

import de.tlc4b.exceptions.ScopeException;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class DefinitionsTest {

	@Test (expected = ScopeException.class)
	public void testVariableInPropertiesClause() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES foo\n"
				+ "DEFINITIONS foo == x = 1"
				+ "VARIABLES x \n" 
				+ "INVARIANT x = 1"
				+ "INITIALISATION x:= 1"  
				+ "END";
		TestUtil.compare("", machine);
	}
	
	@Test
	public void testPredicateDefinition() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES foo\n"
				+ "DEFINITIONS foo == 1 = 1"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testParameterizedPredicateDefinition() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES foo(1)\n"
				+ "DEFINITIONS foo(a) == a = 1"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testParameterizedExpressionDefinition2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES foo = foo\n"
				+ "DEFINITIONS foo == 1"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 = 1 \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testParameterizedSubstitutionDefinition2() throws Exception {
		String machine = "MACHINE test\n"
				+ "DEFINITIONS foo == x := 1"
				+ "VARIABLES x \n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION foo\n"
				+ "END";
		String expected = "---- MODULE test----\n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == x = 1\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
}
