package de.tlc4b.typechecking;

import java.util.Hashtable;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.btypes.BType;

public class TestTypechecker {

	final Hashtable<String, BType> parameters;
	final Hashtable<String, BType> constants;
	final Hashtable<String, BType> variables;

	public TestTypechecker(String machine) throws BException {
		parameters = new Hashtable<>();
		constants = new Hashtable<>();
		variables = new Hashtable<>();

		BParser parser = new BParser("Test");
		Start start;
		try {
			start = parser.parseMachine(machine);
		} catch (BCompoundException e) {
			throw e.getFirstException();
		}

		MachineContext c = new MachineContext(null, start);
		c.analyseMachine();
		Typechecker t = new Typechecker(c);

		for (String name : c.getSetParameter().keySet()) {
			parameters.put(name, t.getType(c.getSetParameter().get(name)));
		}

		for (String name : c.getScalarParameter().keySet()) {
			parameters.put(name, t.getType(c.getScalarParameter().get(name)));
		}

		for (String name : c.getConstants().keySet()) {
			constants.put(name, t.getType(c.getConstants().get(name)));
		}

		for (String name : c.getVariables().keySet()) {
			variables.put(name, t.getType(c.getVariables().get(name)));
		}

	}

}
