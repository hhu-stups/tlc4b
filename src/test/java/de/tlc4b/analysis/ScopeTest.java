package de.tlc4b.analysis;

import org.junit.Ignore;
import org.junit.Test;

import static de.tlc4b.util.TestUtil.checkMachine;
import de.tlc4b.exceptions.ScopeException;

public class ScopeTest {

	@Test(expected = ScopeException.class)
	public void testDuplicateConstant() throws Exception {
		String machine = "MACHINE test \n" + "CONSTANTS k, k \n"
				+ "PROPERTIES 1 = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testDuplicateSeenMachine() throws Exception {
		String machine = "MACHINE test \n" + "SEES M1, M1 \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testConstraintsMissingMachineParameter() throws Exception {
		String machine = "MACHINE test \n" + "CONSTRAINTS k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testConstraints() throws Exception {
		String machine = "MACHINE test(k) \n" + "CONSTRAINTS k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testPropertiesUnknownIdentifier() throws Exception {
		String machine = "MACHINE test \n" + "PROPERTIES k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testPropertiesConstant() throws Exception {
		String machine = "MACHINE test \n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test (expected = ScopeException.class)
	public void testConstantsHasSameNameAsElementOfEnumeratedSet() throws Exception {
		String machine = "MACHINE test \n" + "SETS k = {k1,k2} \n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testInvariantUnknownIdentifier() throws Exception {
		String machine = "MACHINE test \n" + "INVARIANT k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testInvariantParameter() throws Exception {
		String machine = "MACHINE test(k) \n" + "CONSTRAINTS k = 1\n"
				+ "INVARIANT k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testInvariantConstatnParameter() throws Exception {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1" + "INVARIANT k = 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testInvariantVariable() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES k \n"
				+ "INVARIANT k = 1 \n" + "INITIALISATION k := 1 \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testInitialisationUnknwonIdentifier() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES k \n"
				+ "INVARIANT k = 1 \n" + "INITIALISATION k := a \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testOperationsUnknwonIdentifier() throws Exception {
		String machine = "MACHINE test\n" + "OPERATIONS foo = a := 1" + "END";
		checkMachine(machine);
	}

	@Test
	public void testSubstitution() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x \n"
				+ "INVARIANT x = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		checkMachine(machine);
	}

	@Ignore //TODO machineContext line 657
	@Test(expected = ScopeException.class)
	public void testConstantSubstitution() throws Exception {
		String machine = "MACHINE test\n" + "CONSTANTS x \n"
				+ "PROPERTIES x = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testSubstitution2() throws Exception {
		String machine = "MACHINE test\n" + "CONSTANTS x \n"
				+ "PROPERTIES x = 1 \n" + "VARIABLES a \n"
				+ "INVARIANT a = 1 \n" + "INITIALISATION a := x \n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testUnkownOperation() throws Exception {
		String machine = "MACHINE test\n" + "INITIALISATION foo \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testLocalVariableForAll() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES !x.(x : INT => x > 1) \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testLocalVariableExist() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x : INT & x > 1) \n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testLocalVariableLambda() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES %x.(x : INT | x + 1)(1) = 1\n" + "END";
		checkMachine(machine);
	}

	@Test
	public void testNestedLocalExists() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x : INT & #x.(x + 1 = 1))\n" + "END";
		checkMachine(machine);
	}

	@Test(expected = ScopeException.class)
	public void testDuplicateLocalVariable() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #(x,x).(1 = 1 & x = x)\n" + "END";
		checkMachine(machine);
	}
	
}
