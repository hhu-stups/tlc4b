package de.b2tla.typechecking;

import java.util.Hashtable;

import de.b2tla.analysis.Ast2String;
import de.b2tla.analysis.MachineContext;
import de.b2tla.analysis.Typechecker;
import de.b2tla.btypes.BType;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class TestTypechecker {

	Hashtable<String, BType> parameters;
	Hashtable<String, BType> constants;
	Hashtable<String, BType> variables;

	public TestTypechecker(String machine) throws BException {
		parameters = new Hashtable<String, BType>();
		constants = new Hashtable<String, BType>();
		variables = new Hashtable<String, BType>();

		BParser parser = new BParser("Test");
		Start start = parser.parse(machine, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
		MachineContext c = new MachineContext(null, start, null);
		Typechecker t = new Typechecker(c);

		for (String name : c.getSetParamter().keySet()) {
			parameters.put(name,
					t.getType(c.getSetParamter().get(name)));
		}
		
		for (String name : c.getScalarParameter().keySet()) {
			parameters.put(name,
					t.getType(c.getScalarParameter().get(name)));
		}

		for (String name : c.getConstants().keySet()) {
			constants.put(name, t.getType(c.getConstants().get(name)));
		}
		
		for (String name : c.getVariables().keySet()) {
			variables.put(name, t.getType(c.getVariables().get(name)));
		}
		

	}
	
	
}
