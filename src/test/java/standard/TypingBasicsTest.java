package standard;

import static org.junit.Assert.*;

import java.util.Hashtable;

import org.junit.Test;

import btypes.BType;
import btypes.ITypeConstants;
import analysis.Ast2String;
import analysis.MachineContext;
import analysis.Typechecker;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import exceptions.TypeErrorException;

public class TypingBasicsTest implements ITypeConstants {

	@Test(expected = TypeErrorException.class)
	public void testUntypedConstant() throws BException {
		String machine = "MACHINE test \n" + "CONSTANTS k\n"
				+ "PROPERTIES 1 = 1 \n" + "END";
		new TypeCheckerEnv(machine);
	}

	@Test(expected = TypeErrorException.class)
	public void testUntypedVariable() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT 1 = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		new TypeCheckerEnv(machine);
	}
	
	@Test
	public void testVariable() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT x  = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		TypeCheckerEnv env = new TypeCheckerEnv(machine);
		assertEquals(INTEGER, env.variables.get("x").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testUntypedParameter() throws BException {
		String machine = "MACHINE test(a) \n" + "CONSTRAINTS 1 = 1 \n" + "END";
		new TypeCheckerEnv(machine);
	}

	@Test
	public void testScalarParameter() throws BException {
		String machine = "MACHINE test(a) \n" + "CONSTRAINTS a = 1 \n" + "END";
		TypeCheckerEnv env = new TypeCheckerEnv(machine);
		assertEquals(INTEGER, env.parameters.get("a").toString());
	}

	@Test
	public void testParameter() throws BException {
		String machine = "MACHINE test(A) \n" + "END";
		TypeCheckerEnv env = new TypeCheckerEnv(machine);
		assertEquals("A", env.parameters.get("A").toString());
	}


	@Test (expected = TypeErrorException.class)
	public void testInitialisationError() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT x  = 1 \n" + "INITIALISATION x := TRUE \n" + "END";
		new TypeCheckerEnv(machine);
	}
	
	@Test
	public void testInitialisation() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT x  = 1 \n" + "INITIALISATION x := 1 \n" + "END";
		new TypeCheckerEnv(machine);
	}
	
	
	@Test
	public void testOperations() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT x  = 1 \n" + "INITIALISATION x := 1 \n" 
				+ "OPERATIONS foo = PRE 1 = 1 THEN x := 1 END \n"
				+ "END";
		new TypeCheckerEnv(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testOperationsError() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x\n"
				+ "INVARIANT x  = 1 \n" + "INITIALISATION x := 1 \n" 
				+ "OPERATIONS foo = PRE 1 = TRUE THEN x := 1 END \n"
				+ "END";
		new TypeCheckerEnv(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testSubstitution() throws BException {
		String machine = "MACHINE test \n" + "VARIABLES x,y \n"
				+ "INVARIANT x  = 1 & y = 1 \n" + "INITIALISATION x,y := 1,TRUE \n" 
				+ "END";
		new TypeCheckerEnv(machine);
	}
	
	@Test
	public void testMult() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES 1 * 2 = k \n"
				+ "END";
		TypeCheckerEnv env = new TypeCheckerEnv(machine);
		assertEquals(INTEGER, env.constants.get("k").toString());
	}
	
	@Test
	public void testMult2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES 1 * 2 * 3 = k \n"
				+ "END";
		TypeCheckerEnv env = new TypeCheckerEnv(machine);
		assertEquals(INTEGER, env.constants.get("k").toString());
	}

	
	class TypeCheckerEnv {
		Hashtable<String, BType> parameters;
		Hashtable<String, BType> constants;
		Hashtable<String, BType> variables;

		public TypeCheckerEnv(String machine) throws BException {
			parameters = new Hashtable<String, BType>();
			constants = new Hashtable<String, BType>();
			variables = new Hashtable<String, BType>();

			BParser parser = new BParser("Test");
			Start start = parser.parse(machine, false);
			final Ast2String ast2String2 = new Ast2String();
			start.apply(ast2String2);
			System.out.println(ast2String2.toString());

			MachineContext c = new MachineContext(start);
			Typechecker t = new Typechecker(c);

			for (String name : c.getMachineParameters().keySet()) {
				parameters.put(name,
						t.getType(c.getMachineParameters().get(name)));
			}

			for (String name : c.getConstants().keySet()) {
				constants.put(name, t.getType(c.getConstants().get(name)));
			}
			
			for (String name : c.getVariables().keySet()) {
				variables.put(name, t.getType(c.getVariables().get(name)));
			}
			

		}

	}

}
