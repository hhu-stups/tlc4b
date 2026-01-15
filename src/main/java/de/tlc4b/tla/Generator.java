package de.tlc4b.tla;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.AConcreteVariablesMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.ConstantsEvaluator;
import de.tlc4b.analysis.DefinitionsAnalyser;
import de.tlc4b.analysis.DefinitionsSorter;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.tla.config.ModelValueAssignment;
import de.tlc4b.tla.config.SetOfModelValuesAssignment;

public class Generator extends DepthFirstAdapter {

	private final MachineContext machineContext;
	private final TypeRestrictor typeRestrictor;
	private final ConstantsEvaluator constantsEvaluator;
	private final DefinitionsAnalyser deferredSetSizeCalculator;

	private final TLAModule tlaModule;
	private final ConfigFile configFile;

	public Generator(MachineContext machineContext,
			TypeRestrictor typeRestrictor,
			ConstantsEvaluator constantsEvaluator,
			DefinitionsAnalyser deferredSetSizeCalculator,
			Typechecker typechecker) {
		this.machineContext = machineContext;
		this.typeRestrictor = typeRestrictor;
		this.constantsEvaluator = constantsEvaluator;
		this.deferredSetSizeCalculator = deferredSetSizeCalculator;

		this.tlaModule = new TLAModule();
		this.configFile = new ConfigFile();

	}

	public void generate() {
		tlaModule.moduleName = machineContext.getMachineName();
		evalSetValuedParameter();
		evalScalarParameter();
		evalMachineSets();
		evalDefinitions();
		evalConstants();

		evalInvariant();
		evalOperations();
		evalGoal();
		machineContext.getStartNode().apply(this);

		evalSpec();
	}

	private void evalInvariant() {
		AInvariantMachineClause invariantClause = machineContext
				.getInvariantMachineClause();
		if (invariantClause != null) {
			this.tlaModule.invariants.addAll(constantsEvaluator
					.getInvariantList());
			this.configFile.setInvariantNumber(tlaModule.invariants.size());
		}
	}

	private void evalSpec() {
		if (this.configFile.isInit() && this.configFile.isNext()
				&& TLC4BGlobals.isCheckLTL()
				&& !machineContext.getLTLFormulas().isEmpty()) {
			this.configFile.setSpec();
		}
	}

	private void evalGoal() {
		if (TLC4BGlobals.isGOAL()) {
			if (machineContext.getDefinitions().containsKey("GOAL")) {
				this.configFile.setGoal();
			}
		}
	}

	private void evalSetValuedParameter() {
		/*
		 * For each set-valued parameter (first letter in upper case) we create
		 * a TLA definition e.g. MACHINE Test(P) -> P == {P_1, P_2}
		 */
		for (String parameter : machineContext.getSetParameter().keySet()) {
			Node node = machineContext.getSetParameter().get(parameter);
			tlaModule.constants.add(node);
			configFile.addAssignment(new SetOfModelValuesAssignment(node, 3));
		}
	}

	private void evalScalarParameter() {
		/*
		 * For each scalar-valued parameter we have to find out if it has a
		 * determined value in the CONSTRAINT clause (e.g. p = 1). In this case
		 * we create a TLA constant, in the other case we create a TLA variable
		 * and add the constraint predicate to the init clause
		 */

		Collection<Node> params = machineContext.getScalarParameter().values();
		if (params.isEmpty())
			return;

		LinkedHashMap<Node, Node> idValueTable = constantsEvaluator
				.getValueOfIdentifierMap();

		Iterator<Node> itr = params.iterator();
		boolean init = false;
		while (itr.hasNext()) {
			Node param = itr.next();

			Node value = idValueTable.get(param);
			if (value != null) {
				tlaModule.addTLADefinition(new TLADefinition(param, value));
				continue;
			}
			Integer intValue = constantsEvaluator.getIntValue(param);
			if (intValue != null) {
				tlaModule.addTLADefinition(new TLADefinition(param, intValue));
				continue;
			}

			Node restrictedNode = typeRestrictor.getRestrictedNode(param);
			AMemberPredicate memberPredicate = new AMemberPredicate(
					(PExpression) param, (PExpression) restrictedNode);
			tlaModule.addInit(memberPredicate);

			init = true;
			this.tlaModule.variables.add(param);
		}

		AConstraintsMachineClause clause = machineContext
				.getConstraintMachineClause();
		if (init) {
			configFile.setInit();
			if (!typeRestrictor.isARemovedNode(clause.getPredicates())) {
				tlaModule.addInit(clause.getPredicates());
			}

		} else {
			if (!typeRestrictor.isARemovedNode(clause.getPredicates()))
				tlaModule.addAssume(clause.getPredicates());
		}
	}

	private void evalMachineSets() {
		/*
		 * Deferred Sets
		 */
		LinkedHashMap<String, Node> map = machineContext.getDeferredSets();
		for (Node d : map.values()) {
			tlaModule.constants.add(d);
			Integer size;
			size = deferredSetSizeCalculator.getSize(d);
			if (size == null) {
				size = constantsEvaluator.getIntValue(d);
			}

			this.configFile.addAssignment(new SetOfModelValuesAssignment(d, size));
		}

		/*
		 * Enumerated Sets
		 */

		LinkedHashMap<String, Node> map2 = machineContext.getEnumeratedSets();
		for (Node n : map2.values()) {
			AEnumeratedSetSet e = (AEnumeratedSetSet) n;
			TLADefinition def = new TLADefinition(e, e);
			this.tlaModule.addTLADefinition(def);
			List<PExpression> copy = new ArrayList<>(e.getElements());
			for (PExpression element : copy) {
				this.tlaModule.constants.add(element);
				this.configFile.addAssignment(new ModelValueAssignment(element));
			}
		}
	}

	private void evalDefinitions() {
		ADefinitionsMachineClause node = machineContext.getDefinitionMachineClause();
		if (node != null) {
			ArrayList<PDefinition> bDefinitions = new ArrayList<>(node.getDefinitions());
			DefinitionsSorter defOrder = new DefinitionsSorter(machineContext, bDefinitions);
			this.tlaModule.allDefinitions.addAll(defOrder.getAllDefinitions());
		}
	}

	private void evalOperations() {
		AOperationsMachineClause node = machineContext.getOperationMachineClause();
		if (null != node) {
			configFile.setNext();
			List<POperation> copy = new ArrayList<>(node.getOperations());
			this.tlaModule.operations.addAll(copy);
		}
	}

	private void evalConstants() {
		if (machineContext.getPropertiesMachineClause() == null)
			return;
		LinkedHashMap<Node, Node> conValueTable = constantsEvaluator.getValueOfIdentifierMap();
		for (Map.Entry<Node, Node> entry : conValueTable.entrySet()) {
			AIdentifierExpression con = (AIdentifierExpression) entry.getKey();
			Node value = entry.getValue();

			AExpressionDefinitionDefinition exprDef = new AExpressionDefinitionDefinition(
				con.getIdentifier().get(0), new LinkedList<>(),
				(PExpression) value
			);// .clone());
			machineContext.addReference(exprDef, con);

			this.tlaModule.addToAllDefinitions(exprDef);
		}

		ArrayList<Node> remainingConstants = new ArrayList<>(machineContext.getConstants().values());
		remainingConstants.removeAll(conValueTable.keySet());

		Node propertiesPredicate = machineContext.getPropertiesMachineClause().getPredicates();
		if (!remainingConstants.isEmpty()) {
			boolean init = false;
			int numberOfIteratedConstants = 0;

			for (Node remainingConstant : remainingConstants) {
				init = true;
				this.tlaModule.variables.add(remainingConstant);

				ArrayList<PExpression> rangeList = constantsEvaluator.getRangeOfIdentifier(remainingConstant);
				if (!rangeList.isEmpty()) {
					numberOfIteratedConstants++;
					ArrayList<PExpression> clone = new ArrayList<>();
					for (PExpression pExpression : rangeList) {
						clone.add(pExpression.clone());
					}
					ASetExtensionExpression set = new ASetExtensionExpression(clone);
					AMemberPredicate member = new AMemberPredicate((AIdentifierExpression) remainingConstant, set);
					tlaModule.addInit(member);
					continue;
				}

				Node restrictedNode = typeRestrictor.getRestrictedNode(remainingConstant);
				AMemberPredicate memberPredicate = new AMemberPredicate(
						(PExpression) remainingConstant, (PExpression) restrictedNode);
				tlaModule.addInit(memberPredicate);

			}

			if (numberOfIteratedConstants > 1) {
				tlaModule.addInit(machineContext.getConstantsSetup());
			}

			if (init) {
				configFile.setInit();
				if (!typeRestrictor.isARemovedNode(propertiesPredicate))
					tlaModule.addInit(propertiesPredicate);
			}

		} else {
			if (machineContext.getConstantsSetup() == null) {
				tlaModule.assumes
						.addAll(constantsEvaluator.getPropertiesList());
			}
			tlaModule.addAssume(propertiesPredicate);
		}

	}

	@Override
	public void inAPropertiesMachineClause(APropertiesMachineClause node) {
		if (!tlaModule.isInitPredicate(node.getPredicates())) {
			// this.tlaModule.addAssume(node.getPredicates());
		}
	}

	@Override
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		this.tlaModule.variables.addAll(copy);
	}

	@Override
	public void caseAConcreteVariablesMachineClause(AConcreteVariablesMachineClause node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		this.tlaModule.variables.addAll(copy);
	}

	@Override
	public void inAAssertionsMachineClause(AAssertionsMachineClause node) {
		List<PPredicate> copy = new ArrayList<>(node.getPredicates());
		for (PPredicate e : copy) {
			this.tlaModule.addAssertion(e);
		}
		this.configFile.setAssertionSize(copy.size());
	}

	@Override
	public void inAInitialisationMachineClause(AInitialisationMachineClause node) {
		this.configFile.setInit();
		this.tlaModule.addInit(node.getSubstitutions());
	}

	public TLAModule getTlaModule() {
		return tlaModule;
	}

	public ConfigFile getConfigFile() {
		return configFile;
	}

}
