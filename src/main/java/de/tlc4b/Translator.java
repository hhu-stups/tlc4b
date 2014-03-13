package de.tlc4b;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.APredicateParseUnit;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.analysis.Ast2String;
import de.tlc4b.analysis.ConstantsEliminator;
import de.tlc4b.analysis.ConstantsEvaluator;
import de.tlc4b.analysis.DefinitionsAnalyser;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.NotSupportedConstructs;
import de.tlc4b.analysis.PrecedenceCollector;
import de.tlc4b.analysis.PrimedNodesMarker;
import de.tlc4b.analysis.Renamer;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.analysis.UsedStandardModules;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.analysis.transformation.DefinitionsEliminator;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.analysis.unchangedvariables.UnchangedVariablesFinder;
import de.tlc4b.prettyprint.TLAPrinter;
import de.tlc4b.tla.Generator;
import de.tlc4b.tlc.TLCOutputInfo;

public class Translator {

	private String machineString;
	private Start start;
	private String moduleString;
	private String configString;
	private String machineName;
	private String ltlFormula;
	private PPredicate constantsSetup;
	private ArrayList<STANDARD_MODULES> usedStandardModules;
	private TLCOutputInfo tlcOutputInfo;

	public Translator(String machineString) throws BException {
		this.machineString = machineString;
		BParser parser = new BParser("Testing");
		start = parser.parse(machineString, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		//System.out.println(ast2String2.toString());
	}

	public Translator(String machineString, String ltlFormula)
			throws BException {
		this.machineString = machineString;
		this.ltlFormula = ltlFormula;
		BParser parser = new BParser("Testing");
		start = parser.parse(machineString, false);
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		//System.out.println(ast2String2.toString());
	}

	public Translator(String machineName, File machineFile, String ltlFormula, String constantSetup)
			throws IOException, BException {
		this.machineName = machineName;
		this.ltlFormula = ltlFormula;
		
		BParser parser = new BParser(machineName);
		start = parser.parseFile(machineFile, false);

		
		if(constantSetup!= null){
			BParser con = new BParser();
			Start start2 = null;
			try {
				start2 = con.parse("#FORMULA " + constantSetup, false);
			} catch (BException e) {
				System.err.println("An error occured while parsing the constants setup predicate.");
				throw e;
			}
			
			APredicateParseUnit parseUnit = (APredicateParseUnit) start2.getPParseUnit();
			this.constantsSetup = parseUnit.getPredicate();
			
			final Ast2String ast2String2 = new Ast2String();
			start2.apply(ast2String2);
			//System.out.println(ast2String2.toString());
		}
		
	    final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		//System.out.println(ast2String2.toString());
	}

	public void translate() {
		@SuppressWarnings("unused")
		DefinitionsEliminator defEliminator = new DefinitionsEliminator(start);

		new NotSupportedConstructs(start);

		MachineContext machineContext = new MachineContext(machineName, start,
				ltlFormula, constantsSetup);
		this.machineName = machineContext.getMachineName();

		Typechecker typechecker = new Typechecker(machineContext);
		UnchangedVariablesFinder unchangedVariablesFinder = new UnchangedVariablesFinder(
				machineContext);

		PrecedenceCollector precedenceCollector = new PrecedenceCollector(
				start, typechecker.getTypes(), machineContext);

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
