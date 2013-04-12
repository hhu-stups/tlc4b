package de.b2tla.typechecking;

import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;

public class LogicalOperatorTest {

	@Test
	public void testAnd() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 & 1 = 1  \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testOr() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 or 1 = 1  \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testImplication() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 => 1 = 1  \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testEquivalence() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 <=> 1 = 1  \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testNot() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES not(1 = 1) \n"
				+ "END";
		new TestTypechecker(machine);
	}
}
