package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class RenamerTest {


	@Test
	public void testRenameConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS WITH\n"
				+ "PROPERTIES WITH = 1 \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "WITH_1 == 1\n"
				+ "ASSUME WITH_1 = 1\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testRenameVariable() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES WITH\n"
				+ "INVARIANT WITH = 1\n" 
				+ "INITIALISATION WITH := 1 \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES WITH_1 \n"
				+ "Inv == WITH_1 = 1\n"
				+ "Init == WITH_1 = 1 \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testRenameOperation() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1 \n"
				+ "OPERATIONS\n"
				+ "WITH = x:= 2 \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Inv == x = 1\n"
				+ "Init == x = 1 \n"
				+ "WITH_1 == x' = 2\n"
				+ "Next == WITH_1 \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testRenameDefinition() throws Exception {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES WITH = 1 \n"
				+ "DEFINITIONS WITH == 1"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "WITH_1 == 1 \n"
				+ "ASSUME WITH_1 = 1\n"
				+ "====";
		compare(expected, machine);
	}
	
	
	@Test
	public void testDefinitionHasSameNameAsConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS x\n"
				+ "DEFINITIONS foo(x) == x  = 1 "
				+ "PROPERTIES x = 1 & foo(1) \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "x == 1\n"
				+ "foo(x_1) == x_1 = 1\n"
				+ "ASSUME x = 1 /\\ foo(1)\n"
				+ "====";
		System.out.println(expected);
		compare(expected, machine);
	}
	
	@Test
	public void testBoundedVariableHasSameNameAsConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS x\n"
				+ "PROPERTIES x = 1 & #x.(x = 1) \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "x == 1\n"
				+ "ASSUME x = 1 /\\ (\\E x_1 \\in {1} : x_1 = 1)\n"
				+ "====";
		compare(expected, machine);
	}
	
}
