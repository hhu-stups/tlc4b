package de.b2tla;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import de.b2tla.analysis.Ast2String;
import de.b2tla.analysis.ConstantsEliminator;
import de.b2tla.analysis.ConstantsEvaluator;
import de.b2tla.analysis.DefinitionsAnalyser;
import de.b2tla.analysis.MachineContext;
import de.b2tla.analysis.NotSupportedConstructs;
import de.b2tla.analysis.UnchangedVariablesFinder;
import de.b2tla.analysis.PrecedenceCollector;
import de.b2tla.analysis.PrimedNodesMarker;
import de.b2tla.analysis.Renamer;
import de.b2tla.analysis.TypeRestrictor;
import de.b2tla.analysis.Typechecker;
import de.b2tla.analysis.UsedStandardModules;
import de.b2tla.analysis.UsedStandardModules.STANDARD_MODULES;
import de.b2tla.analysis.transformation.DefinitionsEliminator;
import de.b2tla.prettyprint.TLAPrinter;
import de.b2tla.tla.Generator;
import de.b2tla.tlc.TLCOutputInfo;
import de.b2tla.util.StopWatch;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.APredicateParseUnit;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.ltl.core.parser.node.TYesterday;

public class B2TlaTranslator {

	private String machineString;
	private Start start;
	private String moduleString;
	private String configString;
	private String machineName;
	private String ltlFormula;
	private PPredicate constantsSetup;
	private ArrayList<STANDARD_MODULES> usedStandardModules;
	private TLCOutputInfo tlcOutputInfo;

	public B2TlaTranslator(String machineString) throws BException {
		this.machineString = machineString;
		BParser parser = new BParser("Testing");
		start = parser.parse(machineString, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
	}

	public B2TlaTranslator(String machineString, String ltlFormula)
			throws BException {
		this.machineString = machineString;
		this.ltlFormula = ltlFormula;
		BParser parser = new BParser("Testing");
		start = parser.parse(machineString, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
	}

	public B2TlaTranslator(String machineName, File machineFile, String ltlFormula, String constantSetup)
			throws IOException, BException {
		this.machineName = machineName;
		this.ltlFormula = ltlFormula;
		
		BParser parser = new BParser(machineName);
		start = parser.parseFile(machineFile, false);

		
		if(constantSetup!= null){
			BParser con = new BParser("Constants");
			Start start2 = con.parse("#FORMULA " + constantSetup, false);
			APredicateParseUnit parseUnit = (APredicateParseUnit) start2.getPParseUnit();
			this.constantsSetup = parseUnit.getPredicate();
			
			final Ast2String ast2String2 = new Ast2String();
			start2.apply(ast2String2);
			System.out.println(ast2String2.toString());
		}
		
	    final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
	}

	public void translate() {
		DefinitionsEliminator defEliminator = new DefinitionsEliminator(start);

		new NotSupportedConstructs(start);

		MachineContext machineContext = new MachineContext(machineName, start,
				ltlFormula, constantsSetup);
		this.machineName = machineContext.getMachineName();

		Typechecker typechecker = new Typechecker(machineContext);
		UnchangedVariablesFinder unchangedVariablesFinder = new UnchangedVariablesFinder(
				machineContext);

		PrecedenceCollector precedenceCollector = new PrecedenceCollector(
				start, typechecker.getTypes());

		ConstantsEliminator constantsEliminator = new ConstantsEliminator(
				machineContext);
		constantsEliminator.start();

		ConstantsEvaluator constantsEvaluator = new ConstantsEvaluator(
				machineContext);

		TypeRestrictor typeRestrictor = new TypeRestrictor(start,
				machineContext, typechecker);
		UsedStandardModules usedModules = new UsedStandardModules(typechecker,
				typeRestrictor);
		start.apply(usedModules);
		usedStandardModules = usedModules.getUsedModules();

		DefinitionsAnalyser deferredSetSizeCalculator = new DefinitionsAnalyser(
				machineContext);

		Generator generator = new Generator(machineContext, typeRestrictor,
				constantsEvaluator, deferredSetSizeCalculator, typechecker);
		generator.generate();

		generator.getTlaModule().sortAllDefinitions(machineContext);

		PrimedNodesMarker primedNodesMarker = new PrimedNodesMarker(generator
				.getTlaModule().getOperations(), machineContext);
		primedNodesMarker.start();

		Renamer renamer = new Renamer(machineContext);
		TLAPrinter printer = new TLAPrinter(machineContext, typechecker,
				unchangedVariablesFinder, precedenceCollector, usedModules,
				typeRestrictor, generator.getTlaModule(),
				generator.getConfigFile(), primedNodesMarker, renamer);
		printer.start();
		moduleString = printer.getStringbuilder().toString();
		configString = printer.getConfigString().toString();

		tlcOutputInfo = new TLCOutputInfo(machineContext, renamer,
				typechecker.getTypes());
	}

	public String getMachineString() {
		return machineString;
	}

	public String getModuleString() {
		return moduleString;
	}

	public String getConfigString() {
		return configString;
	}

	public Start getStart() {
		return start;
	}

	public String getMachineName() {
		return machineName;
	}

	public TLCOutputInfo getTLCOutputInfo() {
		return tlcOutputInfo;
	}

	public boolean containsUsedStandardModule(STANDARD_MODULES module) {
		return usedStandardModules.contains(module);
	}

	public ArrayList<UsedStandardModules.STANDARD_MODULES> getUsedStandardModule() {
		return usedStandardModules;
	}

}
