package de.tlc4b.exceptions;

import static de.tlc4b.util.TestUtil.checkMachine;

import org.junit.Test;

public class ScopeExceptionTest {

	@Test (expected = ScopeException.class)
	public void testDuplicateIdentifierEnumeratedSet() throws Exception {
		String machine = "MACHINE test\n" 
				+ "SETS S; S ={A,B} \n" 
				+ "END";
		checkMachine(machine);
	}
	
	@Test (expected = ScopeException.class)
	public void testDuplicateIdentifierDeferredSet() throws Exception {
		String machine = "MACHINE test\n" 
				+ "SETS S; S \n" 
				+ "END";
		checkMachine(machine);
	}
	
	@Test (expected = ScopeException.class)
	public void testDuplicateIdentifierEnumValue() throws Exception {
		String machine = "MACHINE test\n" 
				+ "SETS S= {a,a} \n" 
				+ "END";
		checkMachine(machine);
	}
	
	@Test (expected = ScopeException.class)
	public void testDuplicateIdentifierMachineSetParameterDeferredSet() throws Exception {
		String machine = "MACHINE test(AB, AB)\n" 
				+ "END";
		checkMachine(machine);
	}
	
	@Test (expected = ScopeException.class)
	public void testDuplicateIdentifierMachineScalarParameter() throws Exception {
		String machine = "MACHINE test(a, a)\n" 
				+ "CONSTRAINTS a : BOOL \n"
				+ "END";
		checkMachine(machine);
	}
	
}
