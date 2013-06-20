package de.b2tla.tla;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.b2tla.Globals;
import de.b2tla.analysis.ConstantsEvaluator;
import de.b2tla.analysis.DefinitionsAnalyser;
import de.b2tla.analysis.MachineContext;
import de.b2tla.analysis.TypeRestrictor;
import de.b2tla.tla.config.ModelValueAssignment;
import de.b2tla.tla.config.SetOfModelValuesAssignment;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;

public class Generator extends DepthFirstAdapter {

	private MachineContext machineContext;
	private ConstantsEvaluator constantsEvaluator;
	private DefinitionsAnalyser deferredSetSizeCalculator;

	private TLAModule tlaModule;
	private ConfigFile configFile;

	public Generator(MachineContext machineContext,
			TypeRestrictor typeRestrictor,
			ConstantsEvaluator constantsEvaluator,
			DefinitionsAnalyser deferredSetSizeCalculator) {
		this.machineContext = machineContext;
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
		evalOperations();
		evalGoal();
		machineContext.getTree().apply(this);
	}

	private void evalGoal() {
		if (Globals.GOAL) {
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

			init = true;
			this.tlaModule.variables.add(param);
		}

		AConstraintsMachineClause clause = machineContext
				.getConstraintMachineClause();
		if (init) {
			configFile.setInit();
			tlaModule.addInit(clause.getPredicates());
		} else {
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
		ADefinitionsMachineClause node = machineContext.getDefinitionMachineClause();
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
		Iterator<Node> cons = conValueTable.keySet().iterator();
		while (cons.hasNext()) {
			AIdentifierExpression con = (AIdentifierExpression) cons.next();
			Node value = conValueTable.get(con);
			tlaModule.definitions.add(new TLADefinition(con, value));

			AExpressionDefinitionDefinition exprDef = new AExpressionDefinitionDefinition(
					con.getIdentifier().get(0), new LinkedList<PExpression>(),
					(PExpression) value.clone());
			machineContext.getReferences().put(exprDef, con);

			
			this.tlaModule.addToAllDefinitions(exprDef);
		}

		ArrayList<Node> vars = new ArrayList<Node>();
		vars.addAll(machineContext.getConstants().values());
		vars.removeAll(conValueTable.keySet());

		Node propertiesPerdicate = machineContext.getPropertiesMachineClause()
				.getPredicates();
		if (vars.size() != 0) {
			boolean init = false;
			for (int i = 0; i < vars.size(); i++) {
				Node con = vars.get(i);
				Integer value = constantsEvaluator.getIntValue(con);
				if (value == null) {
					init = true;
					this.tlaModule.variables.add(vars.get(i));
				} else {
					tlaModule.definitions.add(new TLADefinition(con, value));
				}

			}
			if (init) {
				configFile.setInit();
				tlaModule.addInit(propertiesPerdicate);
			}

		} else {
			tlaModule.addAssume(propertiesPerdicate);
		}
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		if (!tlaModule.isInitPredicate(node.getPredicates())) {
			this.tlaModule.addAssume(node.getPredicates());
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
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		this.tlaModule.invariant = node.getPredicates();
		if (Globals.invariant) {
			this.configFile.setInvariant();
		}

	}

	@Override
	public void caseAAssertionsMachineClause(AAssertionsMachineClause node) {
		List<PPredicate> copy = new ArrayList<PPredicate>(node.getPredicates());
		for (PPredicate e : copy) {
			this.tlaModule.addAssertion(e);
		}
		this.configFile.setAssertionSize(copy.size());
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
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
