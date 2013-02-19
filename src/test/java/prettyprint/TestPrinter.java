package prettyprint;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import org.junit.internal.runners.statements.Fail;

import util.ToolIO;
import b2tla.analysis.Ast2String;
import b2tla.analysis.MachineContext;
import b2tla.analysis.PrecedenceCollector;
import b2tla.analysis.TLAPrinter;
import b2tla.analysis.TypeRestrictor;
import b2tla.analysis.Typechecker;
import b2tla.analysis.UnchangedVariablesFinder;
import b2tla.analysis.UsedStandardModules;
import b2tla.tla.Generator;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class TestPrinter {

	String result;
	String config;

	public static void compare(String expected, String actual) throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();

		StringBuilder sb1 = translation.Main.start(actual, null, true);
		StringBuilder sb2 = translation.Main.start(expected, null, true);
		if (!sb2.toString().equals(sb1.toString())) {
			// assertEquals(expected, actual);
			fail("expected:\n" + expected + "\nbut was:\n" + actual);
		}
		// assertEquals(sb2.toString(), sb1.toString());
	}

	public TestPrinter(String machine) throws BException {
		BParser parser = new BParser("Test");
		Start start = parser.parse(machine, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
		System.out.println();
		MachineContext machineContext = new MachineContext(start);
		Typechecker typechecker = new Typechecker(machineContext);
		UnchangedVariablesFinder unchangedVariablesFinder = new UnchangedVariablesFinder(
				machineContext);
		PrecedenceCollector precedenceCollector = new PrecedenceCollector(
				start, typechecker.getTypes());

		
		TypeRestrictor typeRestrictor = new TypeRestrictor(start, machineContext,
				typechecker);
		start.apply(typeRestrictor);
		
		UsedStandardModules usedModules = new UsedStandardModules(typechecker, typeRestrictor.getRestrictedTypes());
		start.apply(usedModules);
		
		Generator generator = new Generator(machineContext, typeRestrictor);
		generator.generate();
		
		TLAPrinter printer = new TLAPrinter(machineContext, typechecker,
				unchangedVariablesFinder, precedenceCollector, usedModules, typeRestrictor, generator.getTlaModule());
		printer.start();
		result = printer.getStringbuilder().toString();
		config = printer.getConfigString().toString();
	}

}
