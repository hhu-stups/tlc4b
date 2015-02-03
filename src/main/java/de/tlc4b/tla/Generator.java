package de.tlc4b.tla;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

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
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.tla.config.ModelValueAssignment;
import de.tlc4b.tla.config.SetOfModelValuesAssignment;

public class Generator extends DepthFirstAdapter {

	private MachineContext machineContext;
	private TypeRestrictor typeRestrictor;
	private ConstantsEvaluator constantsEvaluator;
	private DefinitionsAnalyser deferredSetSizeCalculator;

	private TLAModule tlaModule;
	private ConfigFile configFile;

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
		evalConstants();
		evalDefinitions();
		evalInvariant();
		evalOperations();
		evalGoal();
		machineContext.getTree().apply(this);

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
				&& machineContext.getLTLFormulas().size() > 0) {
			this.configFile.setSpec();
		}
	}

	private void evalGoal() {
		if (TLC4BGlobals.isGOAL()) {
			if (machineContext.getDefinitions().keySet().contains("GOAL")) {
				this.configFile.setGoal();
			}
		}
	}

	private void evalSetValuedParameter() {
		/**
		 * For each set-valued parameter (first letter in upper case) we create
		 * a TLA definition e.g. MACHINE Test(P) -> P == {P_1, P_2}
		 */
		Iterator<String> itr = machineContext.getSetParamter().keySet()
				.iterator();
		while (itr.hasNext()) {
			String parameter = itr.next();
			Node node = machineContext.getSetParamter().get(parameter);
			tlaModule.constants.add(node);
			configFile.addAssignment(new SetOfModelValuesAssignment(node, 3));
		}

	}

	private void evalScalarParameter() {
		/**
		 * For each scalar-valued parameter we have to find out if it has a
		 * determined value in the CONSTRAINT clause (e.g. p = 1). In this case
		 * we create a TLA constant, in the other case we create a TLA variable
		 * and add the constraint predicate to the init clause
		 */

		Collection<Node> params = machineContext.getScalarParameter().values();
		if (params.size() == 0)
			return;

		LinkedHashMap<Node, Node> idValueTable = constantsEvaluator
				.getValueOfIdentifierMap();

		Iterator<Node> itr = params.iterator();
		boolean init = false;
		while (itr.hasNext()) {
			Node param = itr.next();

			Node value = idValueTable.get(param);
			if (value != null) {
				tlaModule.definitions.add(new TLADefinition(param, value));
				continue;
			}
			Integer intValue = constantsEvaluator.getIntValue(param);
			if (intValue != null) {
				tlaModule.definitions.add(new TLADefinition(param, intValue));
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
		 * Deffered Sets
		 */
		LinkedHashMap<String, Node> map = machineContext.getDeferredSets();
		Iterator<Node> itr = map.values().iterator();
		while (itr.hasNext()) {
			Node d = itr.next();
			tlaModule.constants.add(d);
			Integer size;
			size = deferredSetSizeCalculator.getSize(d);
			if (size == null) {
				size = constantsEvaluator.getIntValue(d);
			}

			this.configFile.addAssignment(new SetOfModelValuesAssignment(d,
					size));
		}

		/*
		 * Enumerated Sets
		 */

		LinkedHashMap<String, Node> map2 = machineContext.getEnumeratedSets();
		Iterator<Node> itr2 = map2.values().iterator();
		while (itr2.hasNext()) {
			Node n = itr2.next();
			AEnumeratedSetSet e = (AEnumeratedSetSet) n;
			TLADefinition def = new TLADefinition(e, e);
			this.tlaModule.definitions.add(def);
			List<PExpression> copy = new ArrayList<PExpression>(e.getElements());
			for (PExpression element : copy) {
				this.tlaModule.constants.add(element);
				this.configFile
						.addAssignment(new ModelValueAssignment(element));
			}
		}
	}

	private void evalDefinitions() {
		ADefinitionsMachineClause node = machineContext
				.getDefinitionMachineClause();
		if (node != null) {
			for (PDefinition def : node.getDefinitions()) {
				this.tlaModule.addToAllDefinitions(def);
			}
		}
	}

	private void evalOperations() {
		AOperationsMachineClause node = machineContext
				.getOperationMachineClause();
		if (null != node) {
			configFile.setNext();
			List<POperation> copy = new ArrayList<POperation>(
					node.getOperations());
			for (POperation e : copy) {
				this.tlaModule.operations.add(e);
			}
		}
	}

	private void evalConstants() {
		if (machineContext.getPropertiesMachineClause() == null)
			return;
		LinkedHashMap<Node, Node> conValueTable = constantsEvaluator
				.getValueOfIdentifierMap();
		Iterator<Entry<Node, Node>> iterator = conValueTable.entrySet()
				.iterator();
		while (iterator.hasNext()) {
			Entry<Node, Node> entry = iterator.next();
			AIdentifierExpression con = (AIdentifierExpression) entry.getKey();
			Node value = entry.getValue();

			AExpressionDefinitionDefinition exprDef = new AExpressionDefinitionDefinition(
					con.getIdentifier().get(0), new LinkedList<PExpression>(),
					(PExpression) value);//.clone());
			machineContext.addReference(exprDef, con);

			this.tlaModule.addToAllDefinitions(exprDef);
		}

		ArrayList<Node> remainingConstants = new ArrayList<Node>();
		remainingConstants.addAll(machineContext.getConstants().values());
		remainingConstants.removeAll(conValueTable.keySet());

		Node propertiesPerdicate = machineContext.getPropertiesMachineClause()
				.getPredicates();
		if (remainingConstants.size() > 0) {
			boolean init = false;
			int numberOfIteratedConstants = 0;

			for (int i = 0; i < remainingConstants.size(); i++) {
				init = true;
				Node con = remainingConstants.get(i);
				this.tlaModule.variables.add(con);

				ArrayList<PExpression> rangeList = constantsEvaluator
						.getRangeOfIdentifier(con);
				if (rangeList.size() > 0) {
					numberOfIteratedConstants++;
					ArrayList<PExpression> clone = new ArrayList<PExpression>();
					for (PExpression pExpression : rangeList) {
						clone.add((PExpression) pExpression.clone());
					}
					ASetExtensionExpression set = new ASetExtensionExpression(
							clone);
					AMemberPredicate member = new AMemberPredicate(
							(AIdentifierExpression) con, set);
					tlaModule.addInit(member);
					continue;
				}

				Node restrictedNode = typeRestrictor.getRestrictedNode(con);
				AMemberPredicate memberPredicate = new AMemberPredicate(
						(PExpression) con, (PExpression) restrictedNode);
				tlaModule.addInit(memberPredicate);

			}

			if (numberOfIteratedConstants > 1) {
				tlaModule.addInit(machineContext.getConstantsSetup());
			}

			if (init) {
				configFile.setInit();
				if (!typeRestrictor.isARemovedNode(propertiesPerdicate))
					tlaModule.addInit(propertiesPerdicate);
			}

		} else {
			if (machineContext.getConstantsSetup() == null){
				tlaModule.assumes
				.addAll(constantsEvaluator.getPropertiesList());
			}
			tlaModule.addAssume(propertiesPerdicate);
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
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			this.tlaModule.variables.add(e);
		}
	}
	
	@Override
	public void caseAConcreteVariablesMachineClause(AConcreteVariablesMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			this.tlaModule.variables.add(e);
		}
	}

	@Override
	public void inAAssertionsMachineClause(AAssertionsMachineClause node) {
		List<PPredicate> copy = new ArrayList<PPredicate>(node.getPredicates());
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
