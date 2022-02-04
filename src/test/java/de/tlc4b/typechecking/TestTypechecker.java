package de.tlc4b.typechecking;

import java.util.Hashtable;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.btypes.BType;
import de.tlc4b.util.Ast2String;

public class TestTypechecker {

	Hashtable<String, BType> parameters;
	Hashtable<String, BType> constants;
	Hashtable<String, BType> variables;

	public TestTypechecker(String machine) throws BException {
		parameters = new Hashtable<String, BType>();
		constants = new Hashtable<String, BType>();
		variables = new Hashtable<String, BType>();

		BParser parser = new BParser("Test");
		Start start;
		try {
			start = parser.parse(machine, false);
		} catch (BCompoundException e) {
			throw e.getFirstException();
		}
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		// System.out.println(ast2String2.toString());
		MachineContext c = new MachineContext(null, start);
		c.analyseMachine();
		Typechecker t = new Typechecker(c);

		for (String name : c.getSetParamter().keySet()) {
			parameters.put(name, t.getType(c.getSetParamter().get(name)));
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
