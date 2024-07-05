package de.tlc4b.prettyprint;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;
import de.be4.classicalb.core.parser.util.Utils;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.PrecedenceCollector;
import de.tlc4b.analysis.PrimedNodesMarker;
import de.tlc4b.analysis.Renamer;
import de.tlc4b.analysis.StandardModules;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.analysis.UsedStandardModules;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.analysis.unchangedvariables.InvariantPreservationAnalysis;
import de.tlc4b.analysis.unchangedvariables.UnchangedVariablesFinder;
import de.tlc4b.btypes.BType;
import de.tlc4b.btypes.FunctionType;
import de.tlc4b.btypes.IntegerType;
import de.tlc4b.btypes.PairType;
import de.tlc4b.btypes.SetType;
import de.tlc4b.btypes.StructType;
import de.tlc4b.btypes.UntypedType;
import de.tlc4b.ltl.LTLFormulaVisitor;
import de.tlc4b.tla.ConfigFile;
import de.tlc4b.tla.TLADefinition;
import de.tlc4b.tla.TLAModule;
import de.tlc4b.tla.config.ConfigFileAssignment;
import static de.tlc4b.analysis.StandardModules.*;

public class TLAPrinter extends DepthFirstAdapter {

	private final StringBuilder tlaModuleString;
	private final StringBuilder configFileString;

	public StringBuilder getConfigString() {
		return configFileString;
	}

	public StringBuilder getStringbuilder() {
		return tlaModuleString;
	}

	private final MachineContext machineContext;
	private final Typechecker typechecker;
	private final UnchangedVariablesFinder missingVariableFinder;
	private final PrecedenceCollector precedenceCollector;
	private final UsedStandardModules usedStandardModules;
	private final TypeRestrictor typeRestrictor;
	private final TLAModule tlaModule;
	private final ConfigFile configFile;
	private final PrimedNodesMarker primedNodesMarker;
	private final Renamer renamer;
	private boolean recordLTLFormula = false;
	private final StringBuilder translatedLTLFormula = new StringBuilder();
	private final InvariantPreservationAnalysis invariantPreservationAnalysis;

	public TLAPrinter(MachineContext machineContext, Typechecker typechecker,
			UnchangedVariablesFinder unchangedVariablesFinder,
			PrecedenceCollector precedenceCollector,
			UsedStandardModules usedStandardModules,
			TypeRestrictor typeRestrictor, TLAModule tlaModule,
			ConfigFile configFile, PrimedNodesMarker primedNodesMarker,
			Renamer renamer,
			InvariantPreservationAnalysis invariantPreservationAnalysis) {
		this.typechecker = typechecker;
		this.machineContext = machineContext;
		this.missingVariableFinder = unchangedVariablesFinder;
		this.precedenceCollector = precedenceCollector;
		this.usedStandardModules = usedStandardModules;
		this.typeRestrictor = typeRestrictor;
		this.tlaModule = tlaModule;
		this.configFile = configFile;
		this.primedNodesMarker = primedNodesMarker;
		this.renamer = renamer;
		this.invariantPreservationAnalysis = invariantPreservationAnalysis;

		this.tlaModuleString = new StringBuilder();
		this.configFileString = new StringBuilder();
	}

	public void start() {
		printHeader();
		printExtendedModules();
		printConstants();
		printVariables();
		printDefinitions();
		printAssume();
		printInvariant();
		printAssertions();
		printInit();
		printOperations();
		printSpecFormula();
		printLTLFormulas();

		printSymmetry();

		moduleStringAppend("====");

		printConfig();
	}

	private void printSymmetry() {

		if (TLC4BGlobals.useSymmetry()
				&& !machineContext.getDeferredSets().isEmpty()) {

			moduleStringAppend("Symmetry == ");
			Collection<Node> values = machineContext.getDeferredSets().values();
			ArrayList<Node> array = new ArrayList<>(values);
			for (int i = 0; i < array.size(); i++) {
				Node node = array.get(i);
				moduleStringAppend("Permutations(");
				node.apply(this);
				moduleStringAppend(")");
				if (i < array.size() - 1) {
					moduleStringAppend(" \\cup ");
				}
			}
			moduleStringAppend("\n");
			// Symmetry == Permutations(Clients) \cup Permutations(Resources)
		}
	}

	private void printSpecFormula() {

		if (this.configFile.isSpec()) {
			moduleStringAppend("vars == ");
			printVarsAsTuple();
			moduleStringAppend("\n");

			moduleStringAppend("VWF == ");
			printWeakFairness("Next");
			moduleStringAppend("\n");
			moduleStringAppend("Spec == Init /\\ [][Next]_vars /\\ VWF\n");
		}

	}

	public void printStrongFairness(String s) {

		moduleStringAppend(String
				.format("([]<><<%s>>_vars \\/  <>[]~ENABLED(%s) \\/ []<> ENABLED(%s /\\ ",
						s, s, s));
		printVarsStuttering();
		moduleStringAppend("))");

	}

	public void printWeakFairness(String s) {
		moduleStringAppend(String
				.format("([]<><<%s>>_vars \\/  []<>~ENABLED(%s) \\/ []<> ENABLED(%s /\\ ",
						s, s, s));
		printVarsStuttering();
		moduleStringAppend("))");

	}

	public void printWeakFairnessWithParameter(String s) {
		Node operation = machineContext.getOperations().get(s.trim());

		moduleStringAppend("([]<><<");
		printOperationCall(operation);
		moduleStringAppend(">>_vars \\/  []<>~ENABLED(");
		printOperationCall(operation);
		moduleStringAppend(") \\/ []<> ENABLED(");
		printOperationCall(operation);
		moduleStringAppend(" /\\ ");
		printVarsStuttering();
		moduleStringAppend("))");

	}

	private void printVarsStuttering() {
		ArrayList<Node> vars = this.tlaModule.getVariables();
		for (int i = 0; i < vars.size(); i++) {
			vars.get(i).apply(this);
			moduleStringAppend("' = ");
			vars.get(i).apply(this);
			if (i < vars.size() - 1)
				moduleStringAppend(" /\\ ");
		}
	}

	private void printVarsAsTuple() {
		ArrayList<Node> vars = this.tlaModule.getVariables();
		if (vars.isEmpty())
			return;
		moduleStringAppend("<<");
		for (int i = 0; i < vars.size(); i++) {
			vars.get(i).apply(this);
			if (i < vars.size() - 1)
				moduleStringAppend(",");
		}
		moduleStringAppend(">>");
	}

	private void printLTLFormulas() {
		ArrayList<LTLFormulaVisitor> visitors = machineContext.getLTLFormulas();
		if (TLC4BGlobals.isCheckLTL()) {
			for (LTLFormulaVisitor visitor : visitors) {
				moduleStringAppend(visitor.getName() + " == ");
				if (TLC4BGlobals.getTestingMode()) {
					recordLTLFormula = true;
					visitor.printLTLFormula(this, typeRestrictor);
					recordLTLFormula = false;
				} else {
					visitor.printLTLFormula(this, typeRestrictor);
				}
				moduleStringAppend("\n");
			}
		}
	}

	private void printConfig() {
		if (this.configFile.isSpec()) {
			this.configFileString.append("SPECIFICATION Spec\n");
		} else {
			if (this.configFile.isInit()) {
				this.configFileString.append("INIT Init\n");
			}
			if (this.configFile.isInit()) {
				this.configFileString.append("NEXT Next\n");
			}
		}
		if (TLC4BGlobals.isInvariant()) {
			for (int i = 0; i < configFile.getInvariantNumber(); i++) {
				this.configFileString.append("INVARIANT Invariant").append(i + 1).append("\n");
			}
		}

		if (configFile.isGoal()) {
			this.configFileString.append("INVARIANT NotGoal\n");
		}

		if (TLC4BGlobals.isAssertion() && tlaModule.hasInitPredicate()) {
			for (int i = 0; i < configFile.getAssertionSize(); i++) {
				this.configFileString.append("INVARIANT Assertion")
						.append(i + 1).append("\n");
			}
		}

		if (TLC4BGlobals.isCheckLTL()) {
			for (int i = 0; i < machineContext.getLTLFormulas().size(); i++) {
				LTLFormulaVisitor ltlVisitor = machineContext.getLTLFormulas()
						.get(i);
				this.configFileString.append("PROPERTIES ").append(ltlVisitor.getName()).append("\n");
			}
		}
		// CONSTANTS
		ArrayList<ConfigFileAssignment> assignments = configFile
				.getAssignments();
		if (!assignments.isEmpty()) {
			configFileString.append("CONSTANTS\n");
			for (ConfigFileAssignment assignment : assignments) {
				configFileString.append(assignment.getString(renamer));
			}
		}
		if (TLC4BGlobals.useSymmetry()
				&& !machineContext.getDeferredSets().isEmpty()) {
			configFileString.append("SYMMETRY Symmetry\n");
		}

		if (TLC4BGlobals.isPartialInvariantEvaluation()) {
			configFileString.append("CONSTANTS\n");
			configFileString.append("Init_action = Init_action\n");

			ArrayList<POperation> operations = tlaModule.getOperations();
			for (POperation operation : operations) {
				AOperation node = (AOperation) operation;
				String name = renamer.getNameOfRef(node);
				String actionName = name + "actions";
				configFileString.append(actionName).append(" = ").append(actionName).append("\n");
			}
			configFileString.append("\n");
			configFileString.append("VIEW myView");
		}

	}

	public void moduleStringAppend(String str) {
		tlaModuleString.append(str);
		if (recordLTLFormula) {
			translatedLTLFormula.append(str);
		}
	}

	private void printHeader() {
		moduleStringAppend("---- MODULE ");
		moduleStringAppend(this.tlaModule.getModuleName());
		moduleStringAppend(" ----\n");
	}

	private void printExtendedModules() {
		if (!usedStandardModules.getExtendedModules().isEmpty()) {
			moduleStringAppend("EXTENDS ");
			for (int i = 0; i < usedStandardModules.getExtendedModules().size(); i++) {
				if (i > 0) {
					moduleStringAppend(", ");
				}
				moduleStringAppend(usedStandardModules.getExtendedModules()
						.get(i).toString());
			}
			moduleStringAppend("\n");
		}
	}

	private void printDefinitions() {
		ArrayList<TLADefinition> definitions = tlaModule.getTLADefinitions();
		for (TLADefinition def : definitions) {
			if (def.getDefName() instanceof AEnumeratedSetSet) {
				def.getDefName().apply(this);
				continue;
			}
			def.getDefName().apply(this);

			moduleStringAppend(" == ");
			Node e = def.getDefinition();
			if (e == null) {
				moduleStringAppend(def.getInt().toString());
			} else {
				e.apply(this);
			}
			moduleStringAppend("\n");
		}

		ArrayList<PDefinition> bDefinitions = tlaModule.getAllDefinitions();
		if (null == bDefinitions) {
			return;
		}
		for (PDefinition node : bDefinitions) {
			node.apply(this);
		}
		if (configFile.isGoal()) {
			moduleStringAppend("NotGoal == ~GOAL\n");
		}
	}

	private void printConstants() {
		if (TLC4BGlobals.isPartialInvariantEvaluation()) {
			ArrayList<POperation> operations = tlaModule.getOperations();
			moduleStringAppend("CONSTANTS Init_action, ");
			for (int i = 0; i < operations.size(); i++) {
				AOperation node = (AOperation) operations.get(i);
				String name = renamer.getNameOfRef(node);
				moduleStringAppend(name + "_action");

				if (i < operations.size() - 1)
					moduleStringAppend(", ");
			}
			moduleStringAppend("\n");
		}
		/* *************** */
		ArrayList<Node> list = this.tlaModule.getConstants();
		if (list.isEmpty())
			return;
		moduleStringAppend("CONSTANTS ");
		for (int i = 0; i < list.size(); i++) {
			Node con = list.get(i);
			con.apply(this);

			if (i < list.size() - 1)
				moduleStringAppend(", ");
		}
		moduleStringAppend("\n");
	}

	private void printAssume() {
		ArrayList<Node> list = this.tlaModule.getAssume();
		if (list.isEmpty())
			return;

		for (Node node : list) {
			if (!typeRestrictor.isARemovedNode(node)) {
				moduleStringAppend("ASSUME ");
				node.apply(this);
				moduleStringAppend("\n");
			}
		}

	}

	private void printVariables() {
		ArrayList<Node> vars = this.tlaModule.getVariables();
		if (vars.isEmpty())
			return;
		moduleStringAppend("VARIABLES ");
		for (int i = 0; i < vars.size(); i++) {
			vars.get(i).apply(this);
			if (i < vars.size() - 1) {
				moduleStringAppend(", ");
			}

		}
		if (TLC4BGlobals.isPartialInvariantEvaluation()) {
			moduleStringAppend(", last_action");
		}
		moduleStringAppend("\n");

		if (TLC4BGlobals.isPartialInvariantEvaluation()) {
			moduleStringAppend("myView == <<");
			for (int i = 0; i < vars.size(); i++) {
				vars.get(i).apply(this);
				if (i < vars.size() - 1)
					moduleStringAppend(", ");
			}
			moduleStringAppend(">>\n");
		}
	}

	private void printInvariant() {
		ArrayList<Node> invariants = this.tlaModule.getInvariantList();
		for (int i = 0; i < invariants.size(); i++) {
			Node inv = invariants.get(i);
			moduleStringAppend("Invariant" + (i + 1) + " == ");
			if (TLC4BGlobals.isPartialInvariantEvaluation()) {
				ArrayList<Node> operations = invariantPreservationAnalysis
						.getPreservingOperations(inv);
				if (!operations.isEmpty()) {
					moduleStringAppend("last_action \\in {");
					for (int j = 0; j < operations.size(); j++) {
						Node op = operations.get(j);
						String name = renamer.getNameOfRef(op);
						moduleStringAppend(name);
						moduleStringAppend("_action");
						if (j < operations.size() - 1) {
							moduleStringAppend(", ");
						}
					}
					moduleStringAppend("} \\/ ");
				}
			}
			inv.apply(this);
			moduleStringAppend("\n");
		}
	}

	private void printAssertions() {
		if (TLC4BGlobals.isAssertion()) {
			ArrayList<Node> assertions = tlaModule.getAssertions();
			if (assertions.isEmpty())
				return;
			for (int i = 0; i < assertions.size(); i++) {
				Node assertion = assertions.get(i);
				String name = null;
				if (assertion instanceof ALabelPredicate) {
					ALabelPredicate label = (ALabelPredicate) assertion;
					name = label.getName().getText();
				}

				if (name == null) {
					name = "Assertion" + (i + 1);
				}

				if (!tlaModule.hasInitPredicate()) {
					moduleStringAppend("ASSUME ");
				}
				moduleStringAppend(name);
				moduleStringAppend(" == ");
				// assertionMode = true;
				// assertionName = name;
				// parameterCounter = 0;
				assertion.apply(this);
				// assertionMode = false;
				moduleStringAppend("\n");
			}
		}
	}

	private static boolean assertionMode = false;
	private static final String assertionName = null;
	private static Integer parameterCounter = 0;

	private void printInit() {
		ArrayList<Node> inits = this.tlaModule.getInitPredicates();
		if (inits.isEmpty())
			return;
		moduleStringAppend("Init == ");
		if (inits.size() > 1)
			moduleStringAppend("\n\t/\\ ");
		for (int i = 0; i < inits.size(); i++) {
			Node init = inits.get(i);
			if (init instanceof ADisjunctPredicate) {
				moduleStringAppend("(");
			}
			init.apply(this);
			if (init instanceof ADisjunctPredicate) {
				moduleStringAppend(")");
			}
			if (TLC4BGlobals.isPartialInvariantEvaluation()) {
				moduleStringAppend(" /\\ last_action = Init_action");
			}
			if (i < inits.size() - 1)
				moduleStringAppend("\n\t/\\ ");
		}
		moduleStringAppend("\n\n");
	}

	private void printOperations() {
		ArrayList<POperation> ops = this.tlaModule.getOperations();
		if (ops.isEmpty()) {
			ArrayList<Node> vars = tlaModule.getVariables();
			if (!vars.isEmpty()) {
				moduleStringAppend("Next == 1 = 2 /\\ UNCHANGED <<");
				for (int i = 0; i < vars.size(); i++) {
					vars.get(i).apply(this);
					if (i < vars.size() - 1) {
						moduleStringAppend(", ");
					}
				}
				moduleStringAppend(">>\n");
			}
			return;
		}
		for (POperation op : ops) {
			op.apply(this);
		}
		moduleStringAppend("Next == \\/ ");
		Iterator<Node> itr = this.machineContext.getOperations().values()
				.iterator();
		while (itr.hasNext()) {
			Node operation = itr.next();
			printOperationCall(operation);

			if (itr.hasNext()) {
				moduleStringAppend("\n\t\\/ ");
			}
		}
		moduleStringAppend("\n");
	}

	public void printOperationCall(Node operation) {
		AOperation op = (AOperation) operation;
		List<PExpression> newList = new ArrayList<>(op.getParameters());
		// newList.addAll(op.getReturnValues());
		if (!newList.isEmpty()) {
			moduleStringAppend("\\E ");
			for (int i = 0; i < newList.size(); i++) {
				PExpression e = newList.get(i);
				e.apply(this);
				moduleStringAppend(" \\in ");
				typeRestrictor.getRestrictedNode(e).apply(this);
				if (i < newList.size() - 1) {
					moduleStringAppend(", ");
				}
			}
			moduleStringAppend(" : ");
		}

		String opName = renamer.getNameOfRef(op);
		moduleStringAppend(opName);
		if (!newList.isEmpty()) {
			moduleStringAppend("(");
			for (int i = 0; i < newList.size(); i++) {
				newList.get(i).apply(this);
				if (i < newList.size() - 1) {
					moduleStringAppend(", ");
				}

			}
			moduleStringAppend(")");
		}
	}

	@Override
	public void defaultIn(final Node node) {
		if (precedenceCollector.getBrackets().contains(node)) {
			moduleStringAppend("(");
		}
	}

	@Override
	public void defaultOut(final Node node) {
		if (precedenceCollector.getBrackets().contains(node)) {
			moduleStringAppend(")");
		}
	}

	/*
	 * Treewalker
	 */

	@Override
	public void caseAMachineHeader(AMachineHeader node) {
		inAMachineHeader(node);
		moduleStringAppend(node.toString());
		{
			List<TIdentifierLiteral> copy = new ArrayList<>(node.getName());
			for (TIdentifierLiteral e : copy) {
				e.apply(this);
			}
		}
		{
			List<PExpression> copy = new ArrayList<>(node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outAMachineHeader(node);
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
		List<PExpression> copy = new ArrayList<>(node.getElements());
		moduleStringAppend(renamer.getNameOfRef(node) + " == {");
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1) {
				moduleStringAppend(", ");
			}
		}
		moduleStringAppend("}\n");
	}

	@Override
	public void caseADeferredSetSet(ADeferredSetSet node) {
		String name = renamer.getName(node);
		moduleStringAppend(name);
	}

	/**
	 * Substitutions
	 * 
	 */

	@Override
	public void caseABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		for (int i = 0; i < copy.size(); i++) {
			if (i != 0) {
				moduleStringAppend(" /\\ ");
			}
			copy.get(i).apply(this);
			moduleStringAppend(" \\in ");
			node.getSet().apply(this);
		}
		printUnchangedVariables(node, true);
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getLhsExpression());
		List<PExpression> copy2 = new ArrayList<>(node.getRhsExpressions());

		for (int i = 0; i < copy.size(); i++) {
			PExpression left = copy.get(i);
			PExpression right = copy2.get(i);

			if (left instanceof AFunctionExpression) {
				printFunctionAssignment(left, right);

			} else {
				printNormalAssignment(left, right);
			}

			if (i < copy.size() - 1) {
				moduleStringAppend(" /\\ ");
			}
		}

		printUnchangedVariables(node, true);
	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		inABecomesSuchSubstitution(node);
		if (node.getPredicate() instanceof AExistsPredicate) {
			node.getPredicate().apply(this);
		} else {
			List<PExpression> copy = new ArrayList<>(node.getIdentifiers());

			for (int i = 0; i < copy.size(); i++) {
				PExpression e = copy.get(i);
				e.apply(this);
				moduleStringAppend(" \\in ");
				typeRestrictor.getRestrictedNode(e).apply(this);
				if (i < copy.size() - 1) {
					moduleStringAppend(" /\\ ");
				}
			}

			if (!typeRestrictor.isARemovedNode(node.getPredicate())) {
				moduleStringAppend(" /\\ ");
				node.getPredicate().apply(this);
			}
		}

		printUnchangedVariables(node, true);
		outABecomesSuchSubstitution(node);
	}

	private void printNormalAssignment(PExpression left, PExpression right) {
		AIdentifierExpression id = (AIdentifierExpression) left;
		String name = Utils.getTIdentifierListAsString(id.getIdentifier());
		if (!machineContext.getVariables().containsKey(name)) {
			moduleStringAppend("TRUE");
		} else {
			left.apply(this);
			moduleStringAppend(" = ");
			right.apply(this);
		}
	}

	private void printFunctionAssignment(PExpression left, PExpression right) {
		PExpression var = ((AFunctionExpression) left).getIdentifier();
		LinkedList<PExpression> params = ((AFunctionExpression) left).getParameters();
		BType type = typechecker.getType(var);
		var.apply(this);
		moduleStringAppend("' = ");
		if (type instanceof FunctionType) {
			moduleStringAppend(FUNC_ASSIGN);
			moduleStringAppend("(");
			var.apply(this);
			moduleStringAppend(", ");
			if (params.size() > 1) {
				moduleStringAppend("<<");
			}
			for (Iterator<PExpression> iterator = params.iterator(); iterator
					.hasNext();) {
				PExpression pExpression = iterator.next();
				pExpression.apply(this);
				if (iterator.hasNext()) {
					moduleStringAppend(", ");
				}
			}
			if (params.size() > 1) {
				moduleStringAppend(">>");
			}
			moduleStringAppend(", ");
			right.apply(this);
			moduleStringAppend(")");
		} else {
			moduleStringAppend(REL_OVERRIDING + "(");
			var.apply(this);
			moduleStringAppend(", {<<");

			if (params.size() > 1) {
				moduleStringAppend("<<");
				for (Iterator<PExpression> iterator = params.iterator(); iterator.hasNext();) {
					PExpression pExpression = iterator.next();
					pExpression.apply(this);
					if (iterator.hasNext()) {
						moduleStringAppend(", ");
					}
				}
				moduleStringAppend(">>");
			} else {
				params.get(0).apply(this);
			}
			moduleStringAppend(", ");
			right.apply(this);
			moduleStringAppend(">>})");
		}
	}

	public void printUnchangedVariables(Node node, boolean printAnd) {
		HashSet<Node> unchangedVariablesSet = missingVariableFinder.getUnchangedVariables(node);
		if (null != unchangedVariablesSet) {
			ArrayList<Node> unchangedVariables = new ArrayList<>(
				unchangedVariablesSet);
			if (!unchangedVariables.isEmpty()) {
				if (printAnd) {
					moduleStringAppend(" /\\");
				}
				moduleStringAppend(" UNCHANGED <<");
				for (int i = 0; i < unchangedVariables.size(); i++) {
					unchangedVariables.get(i).apply(this);
					if (i < unchangedVariables.size() - 1) {
						moduleStringAppend(", ");
					}
				}
				moduleStringAppend(">>");
			} else {
				if (!printAnd) {
					// there is already a /\
					moduleStringAppend("TRUE");
				}
			}
		}
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<>(node.getSubstitutions());
		moduleStringAppend("(");
		for (int i = 0; i < copy.size(); i++) {
			moduleStringAppend("(");
			copy.get(i).apply(this);
			moduleStringAppend(")");
			if (i < copy.size() - 1) {
				moduleStringAppend(" \\/ ");
			}

		}
		moduleStringAppend(")");
		printUnchangedVariables(node, true);
	}

	@Override
	public void caseASkipSubstitution(ASkipSubstitution node) {
		printUnchangedVariables(node, false);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		if (!node.getElsifSubstitutions().isEmpty()) {
			printElseIFSubstitution(node);
			return;
		}
		moduleStringAppend("(IF ");
		node.getCondition().apply(this);
		moduleStringAppend(" THEN ");
		node.getThen().apply(this);
		List<PSubstitution> copy = new ArrayList<>(node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		moduleStringAppend(" ELSE ");
		if (node.getElse() != null) {
			node.getElse().apply(this);
		} else {
			printUnchangedVariablesNull(node, false);
		}

		moduleStringAppend(")");
		printUnchangedVariables(node, true);
	}

	private void printElseIFSubstitution(AIfSubstitution node) {
		moduleStringAppend("(CASE ");
		node.getCondition().apply(this);
		moduleStringAppend(" -> ");
		node.getThen().apply(this);
		List<PSubstitution> copy = new ArrayList<>(node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			moduleStringAppend(" [] ");
			e.apply(this);
		}
		moduleStringAppend(" [] OTHER -> ");
		if (node.getElse() != null) {
			node.getElse().apply(this);
		} else {
			printUnchangedVariablesNull(node, false);
		}
		moduleStringAppend(")");
		printUnchangedVariables(node, true);

	}

	@Override
	public void caseAIfElsifSubstitution(AIfElsifSubstitution node) {
		node.getCondition().apply(this);
		moduleStringAppend(" -> ");
		node.getThenSubstitution().apply(this);
		printUnchangedVariables(node, true);
	}

	public void printUnchangedVariablesNull(Node node, boolean printAnd) {
		HashSet<Node> unchangedVariablesSet = missingVariableFinder.getUnchangedVariablesNull(node);
		if (null != unchangedVariablesSet) {
			ArrayList<Node> unchangedVariables = new ArrayList<>(
				unchangedVariablesSet);
			if (!unchangedVariables.isEmpty()) {
				if (printAnd) {
					moduleStringAppend(" /\\");
				}
				moduleStringAppend(" UNCHANGED <<");
				for (int i = 0; i < unchangedVariables.size(); i++) {
					unchangedVariables.get(i).apply(this);
					if (i < unchangedVariables.size() - 1) {
						moduleStringAppend(", ");
					}
				}
				moduleStringAppend(">>");
			}
		}
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		inAParallelSubstitution(node);
		for (Iterator<PSubstitution> itr = node.getSubstitutions().iterator(); itr.hasNext();) {
			PSubstitution e = itr.next();

			e.apply(this);

			if (itr.hasNext()) {
				moduleStringAppend(" /\\ ");
			}
		}

		printUnchangedVariables(node, true);
		outAParallelSubstitution(node);
	}

	@Override
	public void caseAPreconditionSubstitution(APreconditionSubstitution node) {
		inAPreconditionSubstitution(node);
		if (!typeRestrictor.isARemovedNode(node.getPredicate())) {
			node.getPredicate().apply(this);
			moduleStringAppend("\n\t/\\ ");
		}
		node.getSubstitution().apply(this);

		outAPreconditionSubstitution(node);
	}

	@Override
	public void caseAAssertionSubstitution(AAssertionSubstitution node) {
		inAAssertionSubstitution(node);
		node.getPredicate().apply(this);
		moduleStringAppend("\n\t/\\ ");
		node.getSubstitution().apply(this);
		outAAssertionSubstitution(node);
	}

	@Override
	public void caseASelectSubstitution(ASelectSubstitution node) {
		inASelectSubstitution(node);
		// TODO remove brackets
		moduleStringAppend("(");
		List<PSubstitution> copy = new ArrayList<>(node.getWhenSubstitutions());

		if (missingVariableFinder.hasUnchangedVariables(node)
				&& (!copy.isEmpty() || node.getElse() != null)) {
			moduleStringAppend("(");
		}
		if (!typeRestrictor.isARemovedNode(node.getCondition())) {
			if (!copy.isEmpty() || node.getElse() != null) {
				moduleStringAppend("(");
			}
			node.getCondition().apply(this);
			moduleStringAppend(" /\\ ");
		}
		node.getThen().apply(this);
		if (!typeRestrictor.isARemovedNode(node.getCondition())) {
			if (!copy.isEmpty() || node.getElse() != null) {
				moduleStringAppend(")");
			}
		}

		for (PSubstitution e : copy) {
			moduleStringAppend(" \\/ ");
			e.apply(this);
		}
		if (node.getElse() != null) {
			moduleStringAppend(" \\/ (");
			moduleStringAppend("~(");
			for (PSubstitution e : copy) {
				ASelectWhenSubstitution w = (ASelectWhenSubstitution) e;
				moduleStringAppend(" \\/ ");
				w.getCondition().apply(this);
			}
			moduleStringAppend(")");
			moduleStringAppend(" /\\ ");
			node.getElse().apply(this);
			moduleStringAppend(")");
		}

		if (missingVariableFinder.hasUnchangedVariables(node)
				&& (!copy.isEmpty() || node.getElse() != null)) {
			moduleStringAppend(")");
		}
		moduleStringAppend(")");
		printUnchangedVariables(node, true);

		outASelectSubstitution(node);
	}

	@Override
	public void caseASelectWhenSubstitution(ASelectWhenSubstitution node) {
		inASelectWhenSubstitution(node);
		node.getCondition().apply(this);
		moduleStringAppend(" /\\ ");
		node.getSubstitution().apply(this);
		outASelectWhenSubstitution(node);
	}

	@Override
	public void caseAAnySubstitution(AAnySubstitution node) {
		inAAnySubstitution(node);
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		if (!copy.isEmpty()) {
			moduleStringAppend("\\E ");
			for (int i = 0; i < copy.size(); i++) {
				PExpression e = copy.get(i);
				e.apply(this);
				moduleStringAppend(" \\in ");
				typeRestrictor.getRestrictedNode(e).apply(this);
				// printTypeOfIdentifier(e, false);
				if (i < copy.size() - 1) {
					moduleStringAppend(", ");
				}
			}
			moduleStringAppend(" : ");
		}

		if (!typeRestrictor.isARemovedNode(node.getWhere())) {
			node.getWhere().apply(this);
			moduleStringAppend(" /\\ ");
		}

		node.getThen().apply(this);
		printUnchangedVariables(node, true);
		outAAnySubstitution(node);
	}

	@Override
	public void caseALetSubstitution(ALetSubstitution node) {
		inALetSubstitution(node);
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		if (!copy.isEmpty()) {
			moduleStringAppend("\\E ");
			for (int i = 0; i < copy.size(); i++) {
				PExpression e = copy.get(i);
				e.apply(this);
				moduleStringAppend(" \\in ");
				typeRestrictor.getRestrictedNode(e).apply(this);
				if (i < copy.size() - 1) {
					moduleStringAppend(", ");
				}
			}
			moduleStringAppend(" : ");
		}

		if (typeRestrictor.isARemovedNode(node.getPredicate())) {
			moduleStringAppend("TRUE");
		} else {
			node.getPredicate().apply(this);
		}

		moduleStringAppend(" /\\ ");
		node.getSubstitution().apply(this);
		printUnchangedVariables(node, true);

		outALetSubstitution(node);
	}

	@Override
	public void caseAOperation(AOperation node) {
		String name = renamer.getNameOfRef(node);
		moduleStringAppend(name);

		// TODO handle output parameter of a operation
		// List<PExpression> output = new ArrayList<PExpression>(
		// node.getReturnValues());
		List<PExpression> params = new ArrayList<>(node.getParameters());
		List<PExpression> newList = new ArrayList<>(params);
		// newList.addAll(output);

		if (!newList.isEmpty()) {
			moduleStringAppend("(");
			for (int i = 0; i < newList.size(); i++) {
				if (i != 0) {
					moduleStringAppend(", ");
				}
				newList.get(i).apply(this);
			}
			moduleStringAppend(")");
		}
		moduleStringAppend(" == ");
		if (node.getOperationBody() != null) {
			node.getOperationBody().apply(this);
		}

		printUnchangedConstants();

		if (TLC4BGlobals.isPartialInvariantEvaluation()) {
			moduleStringAppend(" /\\ last_action' = ");
			moduleStringAppend(name);
			moduleStringAppend("_action");
		}

		moduleStringAppend("\n\n");
	}

	private void printUnchangedConstants() {
		ArrayList<Node> vars = new ArrayList<>(tlaModule.getVariables());
		vars.removeAll(machineContext.getVariables().values());
		if (!vars.isEmpty()) {
			moduleStringAppend(" /\\ UNCHANGED <<");
			for (int i = 0; i < vars.size(); i++) {
				if (i != 0)
					moduleStringAppend(", ");
				vars.get(i).apply(this);
			}

			moduleStringAppend(">>");
		}
	}

	/** Expression **/

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		inAIdentifierExpression(node);
		String name = renamer.getNameOfRef(node);
		if (name == null) {
			name = Utils.getTIdentifierListAsString(node.getIdentifier());
		}
		if (StandardModules.isAbstractConstant(name)) {
			// in order to pass the member check
			moduleStringAppend("{}");
			return;
		}
		moduleStringAppend(name);
		if (primedNodesMarker.isPrimed(node)) {
			moduleStringAppend("'");
		}
		outAIdentifierExpression(node);
	}

	@Override
	public void caseAPrimedIdentifierExpression(APrimedIdentifierExpression node) {
		String name = renamer.getNameOfRef(node);
		if (name == null) {
			name = Utils.getTIdentifierListAsString(node.getIdentifier());
		}
		moduleStringAppend(name);
	}

	@Override
	public void caseAStringExpression(AStringExpression node) {
		inAStringExpression(node);
		moduleStringAppend("\"");
		moduleStringAppend(node.getContent().getText());
		moduleStringAppend("\"");
		outAStringExpression(node);
	}

	@Override
	public void caseAStringSetExpression(AStringSetExpression node) {
		moduleStringAppend("STRING");
	}

	/**
	 * Logical Predicates
	 */

	@Override
	public void caseAEqualPredicate(AEqualPredicate node) {
		inAEqualPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" = ");
		node.getRight().apply(this);
		outAEqualPredicate(node);
	}

	@Override
	public void caseANotEqualPredicate(ANotEqualPredicate node) {
		inANotEqualPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" # ");
		node.getRight().apply(this);
		outANotEqualPredicate(node);
	}
	
	@Override
	public void caseAIfThenElseExpression(AIfThenElseExpression node) {
		moduleStringAppend("(IF ");
		node.getCondition().apply(this);
		moduleStringAppend(" THEN ");
		node.getThen().apply(this);
		moduleStringAppend(" ELSE ");
		node.getElse().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAConjunctPredicate(AConjunctPredicate node) {
		boolean left = typeRestrictor.isARemovedNode(node.getLeft());
		boolean right = typeRestrictor.isARemovedNode(node.getRight());

		if (left && right) {
			moduleStringAppend("TRUE");
		} else if (left) {
			node.getRight().apply(this);
		} else if (right) {
			node.getLeft().apply(this);
		} else {
			inAConjunctPredicate(node);
			node.getLeft().apply(this);
			moduleStringAppend(" /\\ ");
			node.getRight().apply(this);
			outAConjunctPredicate(node);
		}
	}

	@Override
	public void caseADisjunctPredicate(ADisjunctPredicate node) {
		inADisjunctPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\/ ");
		node.getRight().apply(this);
		outADisjunctPredicate(node);
	}

	@Override
	public void caseAImplicationPredicate(AImplicationPredicate node) {
		inAImplicationPredicate(node);
		if (!typeRestrictor.isARemovedNode(node.getLeft())) {
			node.getLeft().apply(this);
			moduleStringAppend(" => ");
		}
		node.getRight().apply(this);
		outAImplicationPredicate(node);
	}

	@Override
	public void caseAEquivalencePredicate(AEquivalencePredicate node) {
		inAEquivalencePredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" <=> ");
		node.getRight().apply(this);
		outAEquivalencePredicate(node);
	}

	@Override
	public void caseABoolSetExpression(ABoolSetExpression node) {
		moduleStringAppend("BOOLEAN");
	}

	@Override
	public void caseABooleanTrueExpression(ABooleanTrueExpression node) {
		inABooleanTrueExpression(node);
		moduleStringAppend("TRUE");
		outABooleanTrueExpression(node);
	}

	@Override
	public void caseABooleanFalseExpression(ABooleanFalseExpression node) {
		inABooleanFalseExpression(node);
		moduleStringAppend("FALSE");
		outABooleanFalseExpression(node);
	}

	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		/*
		 * B: !x,y(T => P) TLA: \A x \in type(x), y \in type(y): T => P
		 */
		inAForallPredicate(node);
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());

		int start = parameterCounter;
		int end = parameterCounter + copy.size();
		parameterCounter = end + 1;
		if (assertionMode) {
			moduleStringAppend("(");
			moduleStringAppend("TLCSet(");
			moduleStringAppend("" + start);
			moduleStringAppend(", TRUE) /\\ ");
			for (int i = start; i < end; i++) {
				moduleStringAppend("TLCSet(");
				moduleStringAppend("" + (i + 1));
				moduleStringAppend(", \"NULL\")");
				moduleStringAppend(" /\\ ");
			}
		}

		moduleStringAppend("\\A ");
		for (int i = 0; i < copy.size(); i++) {
			PExpression e = copy.get(i);
			e.apply(this);
			moduleStringAppend(" \\in ");
			typeRestrictor.getRestrictedNode(e).apply(this);
			if (i < copy.size() - 1) {
				moduleStringAppend(", ");
			}
		}
		moduleStringAppend(" : ");
		if (assertionMode) {
			for (int i = 0; i < copy.size(); i++) {
				PExpression e = copy.get(i);
				moduleStringAppend("TLCSet(");
				moduleStringAppend("" + (i + 1));
				moduleStringAppend(", ");
				e.apply(this);
				moduleStringAppend(")");
				moduleStringAppend(" /\\ ");
			}

			assertionMode = false;

			moduleStringAppend(" IF ");
			node.getImplication().apply(this);
			moduleStringAppend(" THEN TRUE ");
			moduleStringAppend(" ELSE SaveValue(<< \"");
			moduleStringAppend(assertionName);
			moduleStringAppend("\", ");
			for (int i = start; i < end; i++) {
				moduleStringAppend("TLCGet(");
				moduleStringAppend("" + (i + 1));
				moduleStringAppend(")");
				if (i < copy.size() - 1) {
					moduleStringAppend(", ");
				}

			}
			moduleStringAppend(" >>) ");
			moduleStringAppend("/\\ TLCSet(");
			moduleStringAppend("" + start);
			moduleStringAppend(", FALSE)");
			moduleStringAppend(")");
			moduleStringAppend(" /\\ TLCGet(");
			moduleStringAppend("" + start);
			moduleStringAppend(")");
		} else {
			node.getImplication().apply(this);
		}

		outAForallPredicate(node);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		/*
		 * B: #x,y(T => P) TLA: \E x \in type(x), y \in type(y): T => P
		 */
		inAExistsPredicate(node);
		moduleStringAppend("\\E ");

		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		for (int i = 0; i < copy.size(); i++) {
			PExpression e = copy.get(i);
			e.apply(this);
			moduleStringAppend(" \\in ");
			typeRestrictor.getRestrictedNode(e).apply(this);
			if (i < copy.size() - 1) {
				moduleStringAppend(", ");
			}
		}
		moduleStringAppend(" : ");
		if (typeRestrictor.isARemovedNode(node.getPredicate())) {
			moduleStringAppend("TRUE");
		} else {
			node.getPredicate().apply(this);
		}
		outAExistsPredicate(node);
	}

	@Override
	public void caseANegationPredicate(ANegationPredicate node) {
		inANegationPredicate(node);
		moduleStringAppend("\\neg(");
		node.getPredicate().apply(this);
		moduleStringAppend(")");
		outANegationPredicate(node);
	}

	@Override
	public void caseAIntegerExpression(AIntegerExpression node) {
		inAIntegerExpression(node);
		if (node.getLiteral() != null) {
			moduleStringAppend(node.getLiteral().getText());
			// node.getLiteral().apply(this);
		}
		outAIntegerExpression(node);
	}

	@Override
	public void caseAPredicateDefinitionDefinition(APredicateDefinitionDefinition node) {
		String name = renamer.getNameOfRef(node);
		if (null == name) {
			name = node.getName().getText().trim();
		}
		printBDefinition(name, node.getParameters(), node.getRhs());
	}

	@Override
	public void caseAExpressionDefinitionDefinition(AExpressionDefinitionDefinition node) {
		String oldName = node.getName().getText().trim();
		if (StandardModules.isKeywordInModuleExternalFunctions(oldName)) {
			return;
		}
		String name = renamer.getName(node);
		if (null == name) {
			name = node.getName().getText().trim();
		}
		moduleStringAppend(name);
		List<PExpression> args = node.getParameters();
		if (!args.isEmpty()) {
			moduleStringAppend("(");
			for (int i = 0; i < args.size(); i++) {
				if (i != 0)
					moduleStringAppend(", ");
				args.get(i).apply(this);
			}
			moduleStringAppend(")");
		}

		moduleStringAppend(" == ");
		if (TLC4BGlobals.isForceTLCToEvalConstants()) {
			moduleStringAppend("TLCEval(");
		}
		node.getRhs().apply(this);
		if (TLC4BGlobals.isForceTLCToEvalConstants()) {
			moduleStringAppend(")");
		}
		moduleStringAppend("\n");
		// printBDefinition(name, node.getParameters(), node.getRhs());
	}

	@Override
	public void caseASubstitutionDefinitionDefinition(ASubstitutionDefinitionDefinition node) {
		String name = renamer.getNameOfRef(node);
		if (null == name) {
			name = node.getName().getText().trim();
		}
		printBDefinition(name, node.getParameters(), node.getRhs());
	}

	private void printBDefinition(String name, List<PExpression> args, Node rightSide) {
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			return;
		}
		moduleStringAppend(name);
		if (!args.isEmpty()) {
			moduleStringAppend("(");
			for (int i = 0; i < args.size(); i++) {
				if (i != 0)
					moduleStringAppend(", ");
				args.get(i).apply(this);
			}
			moduleStringAppend(")");
		}

		moduleStringAppend(" == ");
		rightSide.apply(this);
		moduleStringAppend("\n");
	}

	@Override
	public void caseADefinitionExpression(ADefinitionExpression node) {
		String name = renamer.getNameOfRef(node);
		if (null == name) {
			name = node.getDefLiteral().getText().trim();
		}
		printBDefinitionCall(name, node.getParameters());
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		String name = renamer.getNameOfRef(node);
		if (null == name) {
			name = node.getDefLiteral().getText().trim();
		}
		printBDefinitionCall(name, node.getParameters());
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		String name = renamer.getNameOfRef(node);
		if (null == name) {
			name = node.getDefLiteral().getText().trim();
		}
		printBDefinitionCall(name, node.getParameters());
	}

	public void printBDefinitionCall(String name, List<PExpression> args) {
		moduleStringAppend(name);
		if (!args.isEmpty()) {
			moduleStringAppend("(");
			for (int i = 0; i < args.size(); i++) {
				if (i != 0)
					moduleStringAppend(", ");
				args.get(i).apply(this);

			}
			moduleStringAppend(")");
		}
	}

	/**
	 * Numbers
	 */

	@Override
	public void caseAIntegerSetExpression(AIntegerSetExpression node) {
		inAIntegerSetExpression(node);
		moduleStringAppend("Int");
		outAIntegerSetExpression(node);
	}

	@Override
	public void caseANaturalSetExpression(ANaturalSetExpression node) {
		inANaturalSetExpression(node);
		moduleStringAppend("Nat");
		outANaturalSetExpression(node);
	}

	@Override
	public void caseANatural1SetExpression(ANatural1SetExpression node) {
		inANatural1SetExpression(node);
		moduleStringAppend("(Nat \\ {0})");
		outANatural1SetExpression(node);
	}

	@Override
	public void caseAIntSetExpression(AIntSetExpression node) {
		inAIntSetExpression(node);
		moduleStringAppend("(" + TLC4BGlobals.getMIN_INT() + ".." + TLC4BGlobals.getMAX_INT() + ")");
		outAIntSetExpression(node);
	}

	@Override
	public void caseANatSetExpression(ANatSetExpression node) {
		inANatSetExpression(node);
		moduleStringAppend("(0.." + TLC4BGlobals.getMAX_INT() + ")");
		outANatSetExpression(node);
	}

	@Override
	public void caseANat1SetExpression(ANat1SetExpression node) {
		inANat1SetExpression(node);
		moduleStringAppend("(1.." + TLC4BGlobals.getMAX_INT() + ")");
		outANat1SetExpression(node);
	}

	@Override
	public void caseAIntervalExpression(AIntervalExpression node) {
		inAIntervalExpression(node);
		moduleStringAppend("(");
		node.getLeftBorder().apply(this);
		moduleStringAppend(" .. ");
		node.getRightBorder().apply(this);
		moduleStringAppend(")");
		outAIntervalExpression(node);
	}

	@Override
	public void caseAGreaterPredicate(AGreaterPredicate node) {
		inAGreaterPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" > ");
		node.getRight().apply(this);
		outAGreaterPredicate(node);
	}

	@Override
	public void caseALessPredicate(ALessPredicate node) {
		inALessPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" < ");
		node.getRight().apply(this);
		outALessPredicate(node);
	}

	@Override
	public void caseAGreaterEqualPredicate(AGreaterEqualPredicate node) {
		inAGreaterEqualPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" >= ");
		node.getRight().apply(this);
		outAGreaterEqualPredicate(node);
	}

	@Override
	public void caseALessEqualPredicate(ALessEqualPredicate node) {
		inALessEqualPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" =< ");
		node.getRight().apply(this);
		outALessEqualPredicate(node);
	}

	@Override
	public void caseAMinExpression(AMinExpression node) {
		moduleStringAppend(MIN);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAMaxExpression(AMaxExpression node) {
		moduleStringAppend(MAX);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAUnaryMinusExpression(AUnaryMinusExpression node) {
		inAUnaryMinusExpression(node);
		moduleStringAppend("-");
		node.getExpression().apply(this);
		outAUnaryMinusExpression(node);
	}

	@Override
	public void caseAAddExpression(AAddExpression node) {
		inAAddExpression(node);
		node.getLeft().apply(this);
		moduleStringAppend(" + ");
		node.getRight().apply(this);
		outAAddExpression(node);
	}

	@Override
	public void caseADivExpression(ADivExpression node) {
		inADivExpression(node);
		moduleStringAppend(B_DIVISION);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
		outADivExpression(node);
	}

	@Override
	public void caseAPowerOfExpression(APowerOfExpression node) {
		moduleStringAppend(B_POWER_Of);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAModuloExpression(AModuloExpression node) {
		inAModuloExpression(node);
		moduleStringAppend(B_MODULO);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
		outAModuloExpression(node);
	}

	@Override
	public void caseAGeneralProductExpression(AGeneralProductExpression node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		moduleStringAppend("Pi(");
		moduleStringAppend("{");
		moduleStringAppend("<<");
		moduleStringAppend("<<");
		printIdentifierList(copy);
		moduleStringAppend(">>");
		moduleStringAppend(", ");
		node.getExpression().apply(this);
		moduleStringAppend(">>");
		moduleStringAppend(" : ");

		printIdentifierList(copy);
		moduleStringAppend(" \\in ");
		if (typeRestrictor.isARemovedNode(node.getPredicates())) {
			printTypesOfIdentifierList(copy);
		} else {
			moduleStringAppend("{");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend(" : ");
			node.getPredicates().apply(this);
			moduleStringAppend("}");
		}
		moduleStringAppend("}");
		moduleStringAppend(")");
	}

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		moduleStringAppend("Sigma(");
		moduleStringAppend("{");
		moduleStringAppend("<<");
		moduleStringAppend("<<");
		printIdentifierList(copy);
		moduleStringAppend(">>");
		moduleStringAppend(", ");
		node.getExpression().apply(this);
		moduleStringAppend(">>");
		moduleStringAppend(" : ");

		printIdentifierList(copy);
		moduleStringAppend(" \\in ");
		if (typeRestrictor.isARemovedNode(node.getPredicates())) {
			printTypesOfIdentifierList(copy);
		} else {
			moduleStringAppend("{");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend(" : ");
			node.getPredicates().apply(this);
			moduleStringAppend("}");
		}
		moduleStringAppend("}");
		moduleStringAppend(")");
	}

	@Override
	public void caseASuccessorExpression(ASuccessorExpression node) {
		inASuccessorExpression(node);
		moduleStringAppend("succ");
		outASuccessorExpression(node);
	}

	@Override
	public void caseAPredecessorExpression(APredecessorExpression node) {
		inAPredecessorExpression(node);
		moduleStringAppend("pred");
		outAPredecessorExpression(node);
	}

	@Override
	public void caseAMaxIntExpression(AMaxIntExpression node) {
		moduleStringAppend(String.valueOf(TLC4BGlobals.getMAX_INT()));
	}

	@Override
	public void caseAMinIntExpression(AMinIntExpression node) {
		moduleStringAppend(String.valueOf(TLC4BGlobals.getMIN_INT()));
	}

	/**
	 * Function
	 */

	private void printIdentifierList(List<PExpression> copy) {
		if (copy.size() == 1) {
			copy.get(0).apply(this);
			return;
		}
		moduleStringAppend("<<");
		for (int i = 0; i < copy.size(); i++) {
			if (i != 0) {
				moduleStringAppend(", ");
			}
			copy.get(i).apply(this);
		}
		moduleStringAppend(">>");
	}

	private void printTypesOfIdentifierList(List<PExpression> copy) {
		if (copy.size() > 1) {
			moduleStringAppend("(");
		}
		for (int i = 0; i < copy.size(); i++) {
			moduleStringAppend("(");
			typeRestrictor.getRestrictedNode(copy.get(i)).apply(this);
			moduleStringAppend(")");
			if (i < copy.size() - 1)
				moduleStringAppend(" \\times ");
		}
		if (copy.size() > 1) {
			moduleStringAppend(")");
		}
	}

	/*****************************************************************************
	 * Functions
	 *****************************************************************************/

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		/*
		 * B: %a,b.(P|e) TLA+ function: [<<a,b>> \in {<<a,b>> \in
		 * type(a)*type(b) : P}|e] relation: TLA+: {<< <<a,b>>, e>>: <<a,b>> \in
		 * {<<a,b>> \in type(a)*type(b): P}}
		 */
		inALambdaExpression(node);
		if (this.typechecker.getType(node) instanceof SetType) {
			moduleStringAppend("{<<");
			List<PExpression> copy = new ArrayList<>(
				node.getIdentifiers());
			printIdentifierList(copy);
			moduleStringAppend(", ");
			node.getExpression().apply(this);
			moduleStringAppend(">> : ");

			printIdentifierList(copy);

			moduleStringAppend(" \\in ");

			if (typeRestrictor.isARemovedNode(node.getPredicate())) {
				printTypesOfIdentifierList(copy);
			} else {
				moduleStringAppend("{");
				printIdentifierList(copy);
				moduleStringAppend(" \\in ");
				printTypesOfIdentifierList(copy);
				moduleStringAppend(" : ");
				node.getPredicate().apply(this);
				moduleStringAppend("}");
			}
			moduleStringAppend("}");

		} else {
			moduleStringAppend("[");
			List<PExpression> copy = new ArrayList<>(
				node.getIdentifiers());
			printIdentifierList(copy);

			moduleStringAppend(" \\in ");
			if (typeRestrictor.isARemovedNode(node.getPredicate())) {
				printTypesOfIdentifierList(copy);

			} else {
				moduleStringAppend("{");
				printIdentifierList(copy);

				moduleStringAppend(" \\in ");
				printTypesOfIdentifierList(copy);
				moduleStringAppend(" : ");
				node.getPredicate().apply(this);
				moduleStringAppend("}");
			}
			moduleStringAppend(" |-> ");
			node.getExpression().apply(this);
			moduleStringAppend("]");
		}
		outALambdaExpression(node);
	}

	@Override
	// Function call
	public void caseAFunctionExpression(AFunctionExpression node) {
		inAFunctionExpression(node);

		if (node.getIdentifier() instanceof AIdentifierExpression) {
			AIdentifierExpression id = (AIdentifierExpression) node
					.getIdentifier();
			String name = Utils.getTIdentifierListAsString(id.getIdentifier());
			if (StandardModules.isAbstractConstant(name)) {

				moduleStringAppend(name);
				// node.getIdentifier().apply(this);
				moduleStringAppend("(");
				List<PExpression> copy = new ArrayList<>(
					node.getParameters());
				copy.get(0).apply(this);
				moduleStringAppend(")");
				return;

			}

		}

		BType type = this.typechecker.getType(node.getIdentifier());
		if (type instanceof FunctionType) {
			node.getIdentifier().apply(this);
			moduleStringAppend("[");
			List<PExpression> copy = new ArrayList<>(
				node.getParameters());
			for (int i = 0; i < copy.size(); i++) {
				if (i != 0) {
					moduleStringAppend(", ");
				}
				copy.get(i).apply(this);
			}
			moduleStringAppend("]");
		} else {

			if (TLC4BGlobals.checkWelldefinedness()) {
				moduleStringAppend(REL_CALL);
			} else {
				moduleStringAppend(REL_CALL_WITHOUT_WD_CHECK);
			}
			moduleStringAppend("(");
			node.getIdentifier().apply(this);
			moduleStringAppend(", ");
			List<PExpression> copy = new ArrayList<>(
				node.getParameters());
			if (copy.size() > 1)
				moduleStringAppend("<<");
			for (int i = 0; i < copy.size(); i++) {
				if (i != 0) {
					moduleStringAppend(", ");
				}
				copy.get(i).apply(this);
			}
			if (copy.size() > 1)
				moduleStringAppend(">>");
			moduleStringAppend(")");
		}

		outAFunctionExpression(node);
	}

	@Override
	public void caseARangeExpression(ARangeExpression node) {
		if (typechecker.getType(node.getExpression()) instanceof FunctionType) {
			moduleStringAppend(FUNC_RANGE);
		} else {
			moduleStringAppend(REL_RANGE);
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAImageExpression(AImageExpression node) {
		if (typechecker.getType(node.getLeft()) instanceof FunctionType) {
			moduleStringAppend(FUNC_IMAGE);
		} else {
			moduleStringAppend(REL_IMAGE);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseATotalFunctionExpression(ATotalFunctionExpression node) {
		BType type = this.typechecker.getType(node);
		BType subtype = ((SetType) type).getSubtype();
		if (subtype instanceof FunctionType) {
			moduleStringAppend("[");
			node.getLeft().apply(this);
			moduleStringAppend(" -> ");
			node.getRight().apply(this);
			moduleStringAppend("]");
		} else {
			if (node.parent() instanceof AMemberPredicate
					&& !typeRestrictor.isARemovedNode(node.parent())
					&& !this.tlaModule.getInitPredicates().contains(
							node.parent())) {
				moduleStringAppend(REL_TOTAL_FUNCTION_ELEMENT_OF);
			} else {
				moduleStringAppend(REL_TOTAL_FUNCTION);
			}
			moduleStringAppend("(");
			node.getLeft().apply(this);
			moduleStringAppend(", ");
			node.getRight().apply(this);
			moduleStringAppend(")");
		}
	}

	private boolean recursiveIsElementOfTest(Node node) {
		Node parent = node.parent();
		if (parent instanceof AMemberPredicate
				&& !typeRestrictor.isARemovedNode(parent)
				&& !this.tlaModule.getInitPredicates().contains(parent)) {
			return true;
		} else {
			String clazz = parent.getClass().getName();
			// todo include all expressions which have an "element of"
			// translation
			if (clazz.contains("Total") || clazz.contains("Partial")) {
				return recursiveIsElementOfTest(node.parent());
			} else
				return false;
		}
	}

	private void setOfFunctions(Node node, String funcName, String relName,
	                            String relEleOfName, Node left, Node right) {
		BType type = this.typechecker.getType(node);
		BType subtype = ((SetType) type).getSubtype();
		if (subtype instanceof FunctionType) {
			moduleStringAppend(funcName);
		} else {
			if (recursiveIsElementOfTest(node)) {
				moduleStringAppend(relEleOfName);
			} else {
				moduleStringAppend(relName);
			}
		}
		moduleStringAppend("(");
		left.apply(this);
		moduleStringAppend(", ");
		right.apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseATotalInjectionExpression(ATotalInjectionExpression node) {
		setOfFunctions(node, TOTAL_INJECTIVE_FUNCTION,
				REL_TOTAL_INJECTIVE_FUNCTION,
				REL_TOTAL_INJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseATotalSurjectionExpression(ATotalSurjectionExpression node) {
		setOfFunctions(node, TOTAL_SURJECTIVE_FUNCTION,
				REL_TOTAL_SURJECTIVE_FUNCTION,
				REL_TOTAL_SURJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseATotalBijectionExpression(ATotalBijectionExpression node) {
		setOfFunctions(node, TOTAL_BIJECTIVE_FUNCTION,
				REL_TOTAL_BIJECTIVE_FUNCTION,
				REL_TOTAL_BIJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	private void setOfPartialFunctions(Node node, String funcName,
	                                   String funcEleOfName, String relName, String relEleOfName,
	                                   Node left, Node right) {
		BType type = this.typechecker.getType(node);
		BType subtype = ((SetType) type).getSubtype();
		if (subtype instanceof FunctionType) {
			Node parent = node.parent();
			if (parent instanceof AMemberPredicate
					&& !typeRestrictor.isARemovedNode(parent)) {
				moduleStringAppend(funcEleOfName);
				moduleStringAppend("(");
				((AMemberPredicate) parent).getLeft().apply(this);
				moduleStringAppend(", ");
				left.apply(this);
				moduleStringAppend(", ");
				right.apply(this);
				moduleStringAppend(")");
				return;
			} else {
				moduleStringAppend(funcName);
			}
		} else {
			if (recursiveIsElementOfTest(node)) {
				moduleStringAppend(relEleOfName);
			} else {
				moduleStringAppend(relName);
			}
		}
		moduleStringAppend("(");
		left.apply(this);
		moduleStringAppend(", ");
		right.apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAPartialFunctionExpression(APartialFunctionExpression node) {
		setOfPartialFunctions(node, PARTIAL_FUNCTION,
				PARTIAL_FUNCTION_ELEMENT_OF, REL_PARTIAL_FUNCTION,
				REL_PARTIAL_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseAPartialInjectionExpression(APartialInjectionExpression node) {
		setOfPartialFunctions(node, PARTIAL_INJECTIVE_FUNCTION,
				PARTIAL_INJECTIVE_FUNCTION_ELEMENT_OF,
				REL_PARTIAL_INJECTIVE_FUNCTION,
				REL_PARTIAL_INJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseAPartialSurjectionExpression(APartialSurjectionExpression node) {
		setOfPartialFunctions(node, PARTIAL_SURJECTIVE_FUNCTION,
				PARTIAL_SURJECTIVE_FUNCTION_ELEMENT_OF,
				REL_PARTIAL_SURJECTIVE_FUNCTION,
				REL_PARTIAL_SURJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseAPartialBijectionExpression(APartialBijectionExpression node) {
		setOfPartialFunctions(node, PARTIAL_BIJECTIVE_FUNCTION,
			PARTIAL_BIJECTIVE_FUNCTION_ELEMENT_OF,
				REL_PARTIAL_BIJECTIVE_FUNCTION,
				REL_PARTIAL_BIJECTIVE_FUNCTION_ELEMENT_OF, node.getLeft(),
				node.getRight());
	}

	/**
	 * Sets
	 */

	@Override
	public void caseASetExtensionExpression(ASetExtensionExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			// 1 :> 2 @@ 2 :> 2
			moduleStringAppend("(");
			for (int i = 0; i < node.getExpressions().size(); i++) {
				ACoupleExpression couple = (ACoupleExpression) node
						.getExpressions().get(i);
				Node left = couple.getList().get(0);
				Node right = couple.getList().get(1);
				left.apply(this);
				moduleStringAppend(":>");
				right.apply(this);

				if (i < node.getExpressions().size() - 1) {
					moduleStringAppend(" @@ ");
				}
			}
			moduleStringAppend(")");
			return;
		}
		moduleStringAppend("{");
		{
			List<PExpression> copy = new ArrayList<>(
				node.getExpressions());
			for (int i = 0; i < copy.size(); i++) {
				if (i != 0) {
					moduleStringAppend(", ");
				}
				copy.get(i).apply(this);
			}
		}
		moduleStringAppend("}");
	}

	@Override
	public void caseAEmptySetExpression(AEmptySetExpression node) {
		evalEmptyFunctionOrRelation(node);
	}

	@Override
	public void caseAMemberPredicate(AMemberPredicate node) {
		inAMemberPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\in ");
		node.getRight().apply(this);
		outAMemberPredicate(node);
	}

	@Override
	public void caseANotMemberPredicate(ANotMemberPredicate node) {
		inANotMemberPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\notin ");
		node.getRight().apply(this);
		outANotMemberPredicate(node);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		inAComprehensionSetExpression(node);
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		if (copy.size() < 3) {
			moduleStringAppend("{");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend(": ");
			if (typeRestrictor.isARemovedNode(node.getPredicates())) {
				moduleStringAppend("TRUE");
			} else {
				node.getPredicates().apply(this);
			}
			moduleStringAppend("}");

		} else {
			moduleStringAppend("{");
			printAuxiliaryVariables(copy.size());
			moduleStringAppend(": t_ \\in ");
			moduleStringAppend("{");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			for (int i = 0; i < copy.size(); i++) {
				moduleStringAppend("(");
				typeRestrictor.getRestrictedNode(copy.get(i)).apply(this);
				moduleStringAppend(")");
				if (i < copy.size() - 1)
					moduleStringAppend(" \\times ");
			}
			moduleStringAppend(": ");
			if (typeRestrictor.isARemovedNode(node.getPredicates())) {
				moduleStringAppend("TRUE");
			} else {
				node.getPredicates().apply(this);
			}
			moduleStringAppend("}");
			moduleStringAppend("}");
		}

		outAComprehensionSetExpression(node);
	}

	@Override
	public void caseAEventBComprehensionSetExpression(AEventBComprehensionSetExpression node) {
		inAEventBComprehensionSetExpression(node);

		moduleStringAppend("{");
		node.getExpression().apply(this);
		moduleStringAppend(": ");
		node.getPredicates().apply(this);
		moduleStringAppend("}");

		outAEventBComprehensionSetExpression(node);
	}

	private void printAuxiliaryVariables(int size) {
		for (int i = 0; i < size - 1; i++) {
			moduleStringAppend("<<");
		}
		for (int i = 0; i < size; i++) {
			if (i != 0) {
				moduleStringAppend(", ");
			}
			moduleStringAppend("t_[" + (i + 1) + "]");
			if (i != 0) {
				moduleStringAppend(">>");
			}
		}
	}

	@Override
	public void caseAUnionExpression(AUnionExpression node) {
		inAUnionExpression(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\cup ");
		node.getRight().apply(this);
		outAUnionExpression(node);
	}

	@Override
	public void caseAIntersectionExpression(AIntersectionExpression node) {
		inAIntersectionExpression(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\cap ");
		node.getRight().apply(this);
		outAIntersectionExpression(node);
	}

	@Override
	public void caseASetSubtractionExpression(ASetSubtractionExpression node) {
		inASetSubtractionExpression(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\ ");
		node.getRight().apply(this);
		outASetSubtractionExpression(node);
	}

	@Override
	public void caseAPowSubsetExpression(APowSubsetExpression node) {
		inAPowSubsetExpression(node);
		moduleStringAppend("SUBSET(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
		outAPowSubsetExpression(node);
	}

	@Override
	public void caseAPow1SubsetExpression(APow1SubsetExpression node) {
		moduleStringAppend(POW_1);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAFinSubsetExpression(AFinSubsetExpression node) {
		moduleStringAppend(FINITE_SUBSETS);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAFin1SubsetExpression(AFin1SubsetExpression node) {
		moduleStringAppend(FINITE_1_SUBSETS);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseACardExpression(ACardExpression node) {
		BType type = typechecker.getType(node.getExpression());
		if (type instanceof FunctionType) {
			moduleStringAppend("Cardinality(DOMAIN(");
			node.getExpression().apply(this);
			moduleStringAppend("))");
		} else {
			moduleStringAppend("Cardinality(");
			node.getExpression().apply(this);
			moduleStringAppend(")");
		}
	}

	@Override
	public void caseASubsetPredicate(ASubsetPredicate node) {
		inASubsetPredicate(node);
		node.getLeft().apply(this);
		// moduleStringAppend(" \\in SUBSET(");
		moduleStringAppend(" \\subseteq ");
		node.getRight().apply(this);
		// moduleStringAppend(")");
		outASubsetPredicate(node);
	}

	@Override
	public void caseASubsetStrictPredicate(ASubsetStrictPredicate node) {
		inASubsetStrictPredicate(node);
		node.getLeft().apply(this);
		moduleStringAppend(" \\in (SUBSET(");
		node.getRight().apply(this);
		moduleStringAppend(") \\ {");
		node.getRight().apply(this);
		moduleStringAppend("})");
		outASubsetStrictPredicate(node);
	}

	@Override
	public void caseANotSubsetPredicate(ANotSubsetPredicate node) {
		moduleStringAppend(NOT_SUBSET);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseANotSubsetStrictPredicate(ANotSubsetStrictPredicate node) {
		moduleStringAppend(NOT_STRICT_SUBSET);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAGeneralUnionExpression(AGeneralUnionExpression node) {
		inAGeneralUnionExpression(node);
		moduleStringAppend("UNION(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
		outAGeneralUnionExpression(node);
	}

	@Override
	public void caseAGeneralIntersectionExpression(AGeneralIntersectionExpression node) {
		inAGeneralIntersectionExpression(node);
		moduleStringAppend("Inter(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
		outAGeneralIntersectionExpression(node);
	}

	@Override
	public void caseAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());

		moduleStringAppend("UNION({");
		node.getExpression().apply(this);
		moduleStringAppend(": ");
		printIdentifierList(copy);
		if (typeRestrictor.isARemovedNode(node.getPredicates())) {
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend("})");
		} else {
			moduleStringAppend(" \\in {");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend(": ");
			node.getPredicates().apply(this);
			moduleStringAppend("}");
			moduleStringAppend("})");
		}
	}

	@Override
	public void caseAQuantifiedIntersectionExpression(AQuantifiedIntersectionExpression node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());

		moduleStringAppend("Inter({");
		node.getExpression().apply(this);
		moduleStringAppend(": ");
		printIdentifierList(copy);
		if (typeRestrictor.isARemovedNode(node.getPredicates())) {
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend("})");
		} else {
			moduleStringAppend(" \\in {");
			printIdentifierList(copy);
			moduleStringAppend(" \\in ");
			printTypesOfIdentifierList(copy);
			moduleStringAppend(": ");
			node.getPredicates().apply(this);
			moduleStringAppend("}");
			moduleStringAppend("})");
		}
	}

	/**
	 * Relations
	 */

	@Override
	public void caseACoupleExpression(ACoupleExpression node) {
		inACoupleExpression(node);
		List<PExpression> copy = new ArrayList<>(node.getList());
		for (int i = 0; i < copy.size() - 1; i++) {
			moduleStringAppend("<<");
		}
		for (int i = 0; i < copy.size(); i++) {
			if (i != 0) {
				moduleStringAppend(", ");
			}
			copy.get(i).apply(this);
			if (i != 0) {
				moduleStringAppend(">>");
			}
		}
		outACoupleExpression(node);
	}

	@Override
	public void caseARelationsExpression(ARelationsExpression node) {
		moduleStringAppend(RELATIONS + "(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseADomainExpression(ADomainExpression node) {
		inADomainExpression(node);
		if (typechecker.getType(node.getExpression()) instanceof FunctionType) {
			moduleStringAppend("DOMAIN ");
			node.getExpression().apply(this);
		} else {
			moduleStringAppend(REL_DOMAIN + "(");
			node.getExpression().apply(this);
			moduleStringAppend(")");
		}
		outADomainExpression(node);
	}

	@Override
	public void caseAIdentityExpression(AIdentityExpression node) {
		inAIdentityExpression(node);
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_ID);
		} else {
			moduleStringAppend(REL_ID);
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
		outAIdentityExpression(node);
	}

	@Override
	public void caseADomainRestrictionExpression(ADomainRestrictionExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_DOMAIN_RESTRICTION);
		} else {
			moduleStringAppend(REL_DOMAIN_RESTRICTION);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseADomainSubtractionExpression(ADomainSubtractionExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_DOMAIN_SUBTRACTION);
		} else {
			moduleStringAppend(REL_DOMAIN_SUBTRACTION);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseARangeRestrictionExpression(ARangeRestrictionExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_RANGE_RESTRICTION);
		} else {
			moduleStringAppend(REL_RANGE_RESTRICTION);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseARangeSubtractionExpression(ARangeSubtractionExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_RANGE_SUBTRACTION);
		} else {
			moduleStringAppend(REL_RANGE_SUBTRACTION);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAReverseExpression(AReverseExpression node) {
		if (typechecker.getType(node.getExpression()) instanceof FunctionType) {
			moduleStringAppend(FUNC_INVERSE);
		} else {
			moduleStringAppend(REL_INVERSE);
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAOverwriteExpression(AOverwriteExpression node) {
		if (typechecker.getType(node) instanceof FunctionType) {
			moduleStringAppend(FUNC_OVERRIDE);
		} else {
			moduleStringAppend(REL_OVERRIDING);
		}
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseADirectProductExpression(ADirectProductExpression node) {
		moduleStringAppend(REL_DIRECT_PRODUCT);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAParallelProductExpression(AParallelProductExpression node) {
		moduleStringAppend(REL_PARALLEL_PRODUCT);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseACompositionExpression(ACompositionExpression node) {
		moduleStringAppend(REL_COMPOSITION);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAFirstProjectionExpression(AFirstProjectionExpression node) {
		moduleStringAppend(REL_PROJECTION_FUNCTION_FIRST);
		moduleStringAppend("(");
		node.getExp1().apply(this);
		moduleStringAppend(", ");
		node.getExp2().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseASecondProjectionExpression(ASecondProjectionExpression node) {
		moduleStringAppend(REL_PROJECTION_FUNCTION_SECOND);
		moduleStringAppend("(");
		node.getExp1().apply(this);
		moduleStringAppend(", ");
		node.getExp2().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAIterationExpression(AIterationExpression node) {
		moduleStringAppend(REL_ITERATE);
		moduleStringAppend("(");
		node.getLeft().apply(this);
		moduleStringAppend(", ");
		node.getRight().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAClosureExpression(AClosureExpression node) {
		moduleStringAppend(REL_CLOSURE1);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAReflexiveClosureExpression(AReflexiveClosureExpression node) {
		moduleStringAppend(REL_CLOSURE);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseATransFunctionExpression(ATransFunctionExpression node) {
		moduleStringAppend(REL_FNC);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseATransRelationExpression(ATransRelationExpression node) {
		moduleStringAppend(REL_REL);
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	/**
	 * Sequences
	 */

	@Override
	public void caseASequenceExtensionExpression(ASequenceExtensionExpression node) {
		List<PExpression> copy = new ArrayList<>(node.getExpression());
		BType type = typechecker.getType(node);
		if (type instanceof FunctionType) {
			moduleStringAppend("<<");

			for (int i = 0; i < copy.size(); i++) {
				copy.get(i).apply(this);
				if (i < copy.size() - 1)
					moduleStringAppend(", ");
			}
			moduleStringAppend(">>");
		} else {
			moduleStringAppend("{");
			for (int i = 0; i < copy.size(); i++) {
				moduleStringAppend("<<");
				moduleStringAppend(String.valueOf(i + 1));
				moduleStringAppend(", ");
				copy.get(i).apply(this);
				moduleStringAppend(">>");
				if (i < copy.size() - 1)
					moduleStringAppend(", ");
			}
			moduleStringAppend("}");
		}
	}

	private void evalEmptyFunctionOrRelation(Node node) {
		moduleStringAppend(typechecker.getType(node) instanceof FunctionType ? "<<>>" : "{}");
	}

	@Override
	public void caseAEmptySequenceExpression(AEmptySequenceExpression node) {
		evalEmptyFunctionOrRelation(node);
	}

	@Override
	public void caseASeqExpression(ASeqExpression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {
			moduleStringAppend(REL_SET_OF_SEQUENCES);
		} else {
			moduleStringAppend("Seq");
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseASizeExpression(ASizeExpression node) {
		printSequenceOrRelation(node.getExpression(), "Len", REL_SEQUENCE_SIZE,
				node.getExpression(), null);
	}

	@Override
	public void caseAConcatExpression(AConcatExpression node) {
		BType type = typechecker.getType(node);
		if (type instanceof SetType) {
			moduleStringAppend(REL_SEQUENCE_Concat);
			moduleStringAppend("(");
			node.getLeft().apply(this);
			moduleStringAppend(", ");
			node.getRight().apply(this);
			moduleStringAppend(")");
		} else {
			inAConcatExpression(node);
			node.getLeft().apply(this);
			moduleStringAppend(" \\o ");
			node.getRight().apply(this);
			outAConcatExpression(node);
		}
	}

	@Override
	public void caseAInsertTailExpression(AInsertTailExpression node) {
		printSequenceOrRelation(node, "Append", REL_SEQUENCE_APPEND,
			node.getLeft(), node.getRight());
	}

	private void printSequenceOrRelation(Node node, String sequence,
	                                     String relation, Node left, Node right) {
		BType type = typechecker.getType(node);
		if (type instanceof SetType) {
			moduleStringAppend(relation);
		} else {
			moduleStringAppend(sequence);
		}
		moduleStringAppend("(");
		left.apply(this);

		if (right != null) {
			moduleStringAppend(",");
			right.apply(this);
		}
		moduleStringAppend(")");
	}

	@Override
	public void caseAFirstExpression(AFirstExpression node) {
		printSequenceOrRelation(node.getExpression(), "Head",
				REL_SEQUENCE_FIRST_ELEMENT, node.getExpression(), null);
	}

	@Override
	public void caseATailExpression(ATailExpression node) {
		printSequenceOrRelation(node.getExpression(), "Tail",
				REL_SEQUENCE_TAIL, node.getExpression(), null);
	}

	/**
	 * SequencesExtended
	 */

	@Override
	public void caseAIseqExpression(AIseqExpression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {

			if (recursiveIsElementOfTest(node.parent())
					&& !typeRestrictor.isARemovedNode(node.parent())) {
				moduleStringAppend(REL_INJECTIVE_SEQUENCE_ELEMENT_OF);
			} else {
				moduleStringAppend(REL_INJECTIVE_SEQUENCE);
			}
		} else {
			if (node.parent() instanceof AMemberPredicate
					&& !typeRestrictor.isARemovedNode(node.parent())) {
				moduleStringAppend(INJECTIVE_SEQUENCE_ELEMENT_OF);
			} else {
				moduleStringAppend(INJECTIVE_SEQUENCE);
			}
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseAIseq1Expression(AIseq1Expression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {
			if (recursiveIsElementOfTest(node)) {
				moduleStringAppend(REL_INJECTIVE_SEQUENCE_1_ELEMENT_OF);
			} else {
				moduleStringAppend(REL_INJECTIVE_SEQUENCE_1);
			}
		} else {
			if (recursiveIsElementOfTest(node)) {
				moduleStringAppend(INJECTIVE_SEQUENCE_1_ELEMENT_OF);
			} else {
				moduleStringAppend(INJECTIVE_SEQUENCE_1);
			}
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseASeq1Expression(ASeq1Expression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {
			moduleStringAppend(REL_SET_OF_NON_EMPTY_SEQUENCES);
		} else {
			moduleStringAppend(SEQUENCE_1);
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseALastExpression(ALastExpression node) {
		printSequenceOrRelation(node.getExpression(), SEQUENCE_LAST_ELEMENT,
				REL_SEQUENCE_LAST_ELEMENT, node.getExpression(), null);
	}

	@Override
	public void caseAInsertFrontExpression(AInsertFrontExpression node) {
		printSequenceOrRelation(node.getRight(), SEQUENCE_PREPEND_ELEMENT,
			REL_SEQUENCE_PREPEND, node.getLeft(), node.getRight());
	}

	@Override
	public void caseAPermExpression(APermExpression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {
			moduleStringAppend(REL_SEQUENCE_PERM);
		} else {
			moduleStringAppend(SEQUENCE_PERMUTATION);
		}
		moduleStringAppend("(");
		node.getExpression().apply(this);
		moduleStringAppend(")");
	}

	@Override
	public void caseARevExpression(ARevExpression node) {
		printSequenceOrRelation(node, SEQUENCE_REVERSE, REL_SEQUENCE_REVERSE,
				node.getExpression(), null);
	}

	@Override
	public void caseAFrontExpression(AFrontExpression node) {
		printSequenceOrRelation(node.getExpression(), SEQUENCE_FRONT,
				REL_SEQUENCE_FRONT, node.getExpression(), null);
	}

	@Override
	public void caseAGeneralConcatExpression(AGeneralConcatExpression node) {
		BType result = typechecker.getType(node.getExpression());

		if (result instanceof FunctionType
				&& ((FunctionType) result).getRange() instanceof FunctionType) {

		} else {
			BType expected2 = new SetType(new PairType(
					IntegerType.getInstance(), new SetType(new PairType(
							IntegerType.getInstance(), new UntypedType()))));
			typechecker.unify(expected2, result, node);
		}

		printSequenceOrRelation(node, SEQUENCE_GENERAL_CONCATENATION,
			REL_SEQUENCE_GENERAL_CONCATENATION, node.getExpression(), null);
	}

	@Override
	public void caseARestrictFrontExpression(ARestrictFrontExpression node) {
		printSequenceOrRelation(node, SEQUENCE_TAKE_FIRST_ELEMENTS,
				REL_SEQUENCE_TAKE_FIRST_ELEMENTS, node.getLeft(),
				node.getRight());
	}

	@Override
	public void caseARestrictTailExpression(ARestrictTailExpression node) {
		printSequenceOrRelation(node, SEQUENCE_DROP_FIRST_ELEMENTS,
				REL_SEQUENCE_DROP_FIRST_ELEMENTS, node.getLeft(),
				node.getRight());
	}

	/**
	 * Special Operator
	 */
	@Override
	public void caseAMinusOrSetSubtractExpression(AMinusOrSetSubtractExpression node) {
		inAMinusOrSetSubtractExpression(node);
		node.getLeft().apply(this);

		BType leftType = this.typechecker.getType(node.getLeft());
		if (leftType instanceof IntegerType) {
			moduleStringAppend(" - ");
		} else {
			moduleStringAppend(" \\ ");
		}

		node.getRight().apply(this);
		outAMinusOrSetSubtractExpression(node);
	}

	@Override
	public void caseAMultOrCartExpression(AMultOrCartExpression node) {
		inAMultOrCartExpression(node);
		node.getLeft().apply(this);

		BType leftType = this.typechecker.getType(node.getLeft());
		if (leftType instanceof IntegerType) {
			moduleStringAppend(" * ");
		} else {
			moduleStringAppend(" \\times ");
		}

		node.getRight().apply(this);
		outAMultOrCartExpression(node);
	}

	@Override
	public void caseACartesianProductExpression(ACartesianProductExpression node) {
		inACartesianProductExpression(node); // TODO cartesianproduct vs
												// AMultOrCartExpression
		node.getLeft().apply(this);
		moduleStringAppend(" \\times ");
		node.getRight().apply(this);
		outACartesianProductExpression(node);
	}

	@Override
	public void caseAConvertBoolExpression(AConvertBoolExpression node) {
		inAConvertBoolExpression(node);
		moduleStringAppend("(");
		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		moduleStringAppend(")");
		outAConvertBoolExpression(node);
	}

	// Records

	@Override
	public void caseARecExpression(ARecExpression node) {
		moduleStringAppend("[");
		List<PRecEntry> copy = new ArrayList<>(node.getEntries());
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1) {
				moduleStringAppend(", ");
			}
		}
		moduleStringAppend("]");
	}

	@Override
	public void caseARecEntry(ARecEntry node) {
		node.getIdentifier().apply(this);
		if (typechecker.getType(node.parent()) instanceof StructType) {
			moduleStringAppend(" |-> ");
		} else {
			moduleStringAppend(" : ");
		}

		node.getValue().apply(this);
	}

	@Override
	public void caseARecordFieldExpression(ARecordFieldExpression node) {
		inARecordFieldExpression(node);
		node.getRecord().apply(this);
		moduleStringAppend(".");
		node.getIdentifier().apply(this);
		outARecordFieldExpression(node);
	}

	@Override
	public void caseAStructExpression(AStructExpression node) {
		moduleStringAppend("[");
		List<PRecEntry> copy = new ArrayList<>(node.getEntries());
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1) {
				moduleStringAppend(", ");
			}
		}
		moduleStringAppend("]");
	}

	public String geTranslatedLTLFormula() {
		return this.translatedLTLFormula.toString();
	}

	public TLAModule getTLAModule() {
		return this.tlaModule;
	}
}
