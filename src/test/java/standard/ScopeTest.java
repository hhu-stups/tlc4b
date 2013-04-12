package standard;

import org.junit.Ignore;
import org.junit.Test;

import de.b2tla.analysis.Ast2String;
import de.b2tla.analysis.MachineContext;
import de.b2tla.exceptions.ScopeException;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class ScopeTest {

	@Test(expected = ScopeException.class)
	public void testDuplicateConstant() throws BException {
		String machine = "MACHINE test \n" + "CONSTANTS k, k \n"
				+ "PROPERTIES 1 = 1 \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testDuplicateSeenMachine() throws BException {
		String machine = "MACHINE test \n" + "SEES M1, M1 \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testConstraintsMissingMachineParameter() throws BException {
		String machine = "MACHINE test \n" + "CONSTRAINTS k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testConstraints() throws BException {
		String machine = "MACHINE test(k) \n" + "CONSTRAINTS k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testPropertiesUnknownIdentifier() throws BException {
		String machine = "MACHINE test \n" + "PROPERTIES k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testPropertiesConstant() throws BException {
		String machine = "MACHINE test \n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testPropertiesDeferredSet() throws BException {
		String machine = "MACHINE test \n" + "SETS k \n"
				+ "PROPERTIES k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testPropertiesEnumeratedSet() throws BException {
		String machine = "MACHINE test \n" + "SETS k = {k1,k2} \n"
				+ "PROPERTIES k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testPropertiesElementOfEnumeratedSet() throws BException {
		String machine = "MACHINE test \n" + "SETS k = {k1,k2} \n"
				+ "PROPERTIES k1 = 1 \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testInvariantUnknownIdentifier() throws BException {
		String machine = "MACHINE test \n" + "INVARIANT k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testInvariantParameter() throws BException {
		String machine = "MACHINE test(k) \n" + "CONSTRAINTS k = 1\n"
				+ "INVARIANT k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testInvariantConstatnParameter() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = 1" + "INVARIANT k = 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testInvariantVariable() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES k \n"
				+ "INVARIANT k = 1 \n" + "INITIALISATION k := 1 \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testInitialisationUnknwonIdentifier() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES k \n"
				+ "INVARIANT k = 1 \n" + "INITIALISATION k := a \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testOperationsUnknwonIdentifier() throws BException {
		String machine = "MACHINE test\n" + "OPERATIONS foo = a := 1" + "END";
		checkScope(machine);
	}

	@Test
	public void testSubstitution() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x \n"
				+ "INVARIANT x = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		checkScope(machine);
	}

	@Ignore //TODO
	@Test(expected = ScopeException.class)
	public void testConstantSubstitution() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS x \n"
				+ "PROPERTIES x = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testSubstitution2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS x \n"
				+ "PROPERTIES x = 1 \n" + "VARIABLES a \n"
				+ "INVARIANT a = 1 \n" + "INITIALISATION a := x \n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testUnkownOperation() throws BException {
		String machine = "MACHINE test\n" + "INITIALISATION foo \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testOperation() throws BException {
		String machine = "MACHINE test\n" + "INITIALISATION foo \n"
				+ "OPERATIONS foo = skip \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableForAll() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES !x.(x : INT => x > 1) \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableExist() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x : INT & x > 1) \n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableLambda() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES %x.(x : INT | x + 1) = 1\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableUnion() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES UNION(x).(x : INT | x + 1) = 1\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableInter() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INTER(x).(x : INT | x + 1) = 1\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariablePi() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES PI(x).(x : INT | x + 1) = 1\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalVariableSigma() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES SIGMA(x).(x : INT | x + 1) = 1\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testLocalOperationParameter() throws BException {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo(a) = PRE a = 1 THEN skip END\n" + "END";
		checkScope(machine);
	}

	@Test
	public void testNestedLocalExists() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x : INT & #x.(x : INT & x = 1))\n" + "END";
		checkScope(machine);
	}

	@Test(expected = ScopeException.class)
	public void testDuplicateLocalVariable() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #(x,x).(1 = 1 & x = x)\n" + "END";
		checkScope(machine);
	}

	public void checkScope(String machine) throws BException {
		BParser parser = new BParser("Test");
		Start start = parser.parse(machine, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);

		new MachineContext(start);
	}

}
