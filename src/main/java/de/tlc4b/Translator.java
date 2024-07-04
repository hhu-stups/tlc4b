package de.tlc4b;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Map;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.node.APredicateParseUnit;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.analysis.ConstantsEliminator;
import de.tlc4b.analysis.ConstantsEvaluator;
import de.tlc4b.analysis.DefinitionsAnalyser;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.PrecedenceCollector;
import de.tlc4b.analysis.PrimedNodesMarker;
import de.tlc4b.analysis.Renamer;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.analysis.UnsupportedConstructsFinder;
import de.tlc4b.analysis.UsedStandardModules;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.analysis.transformation.DefinitionsEliminator;
import de.tlc4b.analysis.transformation.SeesEliminator;
import de.tlc4b.analysis.transformation.SequenceSubstitutionsEliminator;
import de.tlc4b.analysis.transformation.SetComprehensionOptimizer;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.analysis.unchangedvariables.InvariantPreservationAnalysis;
import de.tlc4b.analysis.unchangedvariables.UnchangedVariablesFinder;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.prettyprint.TLAPrinter;
import de.tlc4b.tla.Generator;
import de.tlc4b.tlc.TLCOutputInfo;

public class Translator {

	private String machineString;
	private final Start start;
	private Map<String, Start> parsedMachines;
	private String moduleString;
	private String configString;
	private String machineName;
	private String ltlFormula;
	private PPredicate constantsSetup;
	private HashSet<STANDARD_MODULES> standardModulesToBeCreated;
	private TLCOutputInfo tlcOutputInfo;
	private String translatedLTLFormula;

	public Translator(String machineString) throws BCompoundException {
		this.machineString = machineString;
		BParser parser = new BParser("Testing");
		start = parser.parseMachine(machineString);
	}

	public Translator(String machineString, String ltlFormula) throws BCompoundException {
		this.machineString = machineString;
		this.ltlFormula = ltlFormula;
		BParser parser = new BParser("Testing");
		start = parser.parseMachine(machineString);
	}

	public Translator(String machineName, File machineFile, String ltlFormula, String constantSetup)
			throws BCompoundException, IOException {
		this.machineName = machineName;
		this.ltlFormula = ltlFormula;

		BParser parser = new BParser(machineName);
		try {
			start = parser.parseFile(machineFile);
		} catch (NoClassDefFoundError e) {
			throw new TLC4BIOException("Definitions file cannot be found.");
		}

		// Definitions of definitions files are injected in the ast of the main
		// machine
		final RecursiveMachineLoader rml = new RecursiveMachineLoader(machineFile.getParent(),
				parser.getContentProvider());
		rml.loadAllMachines(machineFile, start, parser.getDefinitions());

		parsedMachines = rml.getParsedMachines();

		if (constantSetup != null) {
			BParser con = new BParser();
			Start start2;
			try {
				start2 = con.parseFormula(constantSetup);
			} catch (BCompoundException e) {
				System.err.println("An error occurred while parsing the constants setup predicate.");
				throw e;
			}

			APredicateParseUnit parseUnit = (APredicateParseUnit) start2.getPParseUnit();
			this.constantsSetup = parseUnit.getPredicate();
		}
	}

	public void translate() {
		UnsupportedConstructsFinder unsupportedConstructsFinder = new UnsupportedConstructsFinder(start);
		unsupportedConstructsFinder.find();

		// ast transformation
		SeesEliminator.eliminateSeesClauses(start, parsedMachines);

		DefinitionsEliminator.eliminateDefinitions(start);
		SequenceSubstitutionsEliminator.eliminateSequenceSubstitutions(start);

		// TODO move set comprehension optimizer behind the type checker
		SetComprehensionOptimizer.optimizeSetComprehensions(start);

		MachineContext machineContext = new MachineContext(machineName, start);
		if (ltlFormula != null) {
			machineContext.addLTLFromula(this.ltlFormula);
		}
		if (this.constantsSetup != null) {
			machineContext.setConstantSetupPredicate(constantsSetup);
		}
		machineContext.analyseMachine();

		this.machineName = machineContext.getMachineName();
		if (machineContext.machineContainsOperations()) {
			TLC4BGlobals.setPrintCoverage(true);
		}

		Typechecker typechecker = new Typechecker(machineContext);
		UnchangedVariablesFinder unchangedVariablesFinder = new UnchangedVariablesFinder(machineContext);

		ConstantsEliminator constantsEliminator = new ConstantsEliminator(machineContext);
		constantsEliminator.start();

		ConstantsEvaluator constantsEvaluator = new ConstantsEvaluator(machineContext);

		InvariantPreservationAnalysis invariantPreservationAnalysis = new InvariantPreservationAnalysis(machineContext,
				constantsEvaluator.getInvariantList(), unchangedVariablesFinder);

		TypeRestrictor typeRestrictor = new TypeRestrictor(start, machineContext, typechecker, constantsEvaluator);

		PrecedenceCollector precedenceCollector = new PrecedenceCollector(start, typechecker, machineContext,
				typeRestrictor);

		DefinitionsAnalyser deferredSetSizeCalculator = new DefinitionsAnalyser(machineContext);

		Generator generator = new Generator(machineContext, typeRestrictor, constantsEvaluator,
				deferredSetSizeCalculator, typechecker);
		generator.generate();

		UsedStandardModules usedModules = new UsedStandardModules(start, typechecker, typeRestrictor,
				generator.getTlaModule());

		standardModulesToBeCreated = usedModules.getStandardModulesToBeCreated();

		PrimedNodesMarker primedNodesMarker = new PrimedNodesMarker(generator.getTlaModule().getOperations(),
				machineContext);
		primedNodesMarker.start();

		Renamer renamer = new Renamer(machineContext);
		TLAPrinter printer = new TLAPrinter(machineContext, typechecker, unchangedVariablesFinder, precedenceCollector,
				usedModules, typeRestrictor, generator.getTlaModule(), generator.getConfigFile(), primedNodesMarker,
				renamer, invariantPreservationAnalysis);
		printer.start();
		moduleString = printer.getStringbuilder().toString();
		configString = printer.getConfigString().toString();
		translatedLTLFormula = printer.geTranslatedLTLFormula();

		tlcOutputInfo = new TLCOutputInfo(machineContext, renamer, typechecker, generator.getTlaModule(),
				generator.getConfigFile());
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
		return standardModulesToBeCreated.contains(module);
	}

	public HashSet<UsedStandardModules.STANDARD_MODULES> getStandardModuleToBeCreated() {
		return standardModulesToBeCreated;
	}

	public String getTranslatedLTLFormula() {
		return translatedLTLFormula;
	}

}
