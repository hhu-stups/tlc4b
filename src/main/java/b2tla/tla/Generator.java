package b2tla.tla;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;

import b2tla.analysis.MachineContext;
import b2tla.analysis.TypeRestrictor;
import b2tla.analysis.nodes.EqualsNode;
import b2tla.analysis.nodes.NodeType;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASetsContextClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PSet;

public class Generator extends DepthFirstAdapter {

	private MachineContext machineContext;
	private TypeRestrictor typeRestrictor;

	private TLAModule tlaModule;
	private ConfigFile configFile;

	public Generator(MachineContext machineContext,
			TypeRestrictor typeRestrictor) {
		this.machineContext = machineContext;
		this.typeRestrictor = typeRestrictor;

		this.tlaModule = new TLAModule();
		this.configFile = new ConfigFile();

	}

	public void generate() {
		tlaModule.moduleName = machineContext.getName();
		evalMachineParameter();

		machineContext.getTree().apply(this);
	}

	private void evalMachineParameter() {
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
			configFile.assignments.add(new ConfigFileAssignment(node, null));
		}

		/**
		 * For each scalar-valued parameter we have to find out if it has a
		 * determined value in the CONSTRAINT clause (e.g. p = 1). In this case
		 * we create a TLA constant, in the other case we create a TLA variable
		 * and add the constraint predicate to the init clause
		 */
		LinkedHashMap<String, Node> table = machineContext.getScalarParameter();

		AConstraintsMachineClause constraints = machineContext
				.getConstraintMachineClause();
		Node constraintPredicate = null;
		if (null != constraints) {
			constraintPredicate = constraints.getPredicates();
		}
		Iterator<Node> itr2 = table.values().iterator();
		while (itr2.hasNext()) {
			Node node = itr2.next();
			NodeType nodeType = typeRestrictor.getRestrictedTypes().get(node);
			if (nodeType == null) {
				tlaModule.variables.add(node);
				if (null != constraintPredicate
						&& !tlaModule.initPredicates
								.contains(constraintPredicate)) {
					tlaModule.initPredicates.add(constraintPredicate);
				}
			} else {
				if (nodeType instanceof EqualsNode) {
					tlaModule.definitions.add(new TLADefinition(node, nodeType
							.getExpression()));
				} else {
					tlaModule.variables.add(node);
					if (null != constraintPredicate
							&& !tlaModule.initPredicates
									.contains(constraintPredicate)) {
						tlaModule.initPredicates.add(constraintPredicate);
					}
				}
			}
		}
		if (null != constraintPredicate
				&& !tlaModule.initPredicates.contains(constraintPredicate)) {
			tlaModule.assumes.add(constraintPredicate);
		}

	}

	@Override
	public void caseASetsContextClause(ASetsContextClause node) {
		List<PSet> copy = new ArrayList<PSet>(node.getSet());
		for (PSet e : copy) {
			if (e instanceof AEnumeratedSetSet) {
				// add enumerated set to tla definitions

				for (PExpression p : ((AEnumeratedSetSet) e).getElements()) {
					this.tlaModule.constants.add(p);
					this.configFile.assignments.add(new ConfigFileAssignment(p,
							p));
				}
			} else {
				ADeferredSetSet deferred = (ADeferredSetSet) e;
				this.tlaModule.constants.add(deferred);
			}

		}
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		boolean isVariable = false;
		for (Iterator<PExpression> itr = node.getIdentifiers().iterator(); itr
				.hasNext();) {
			Node con = itr.next();
			NodeType nodeType = typeRestrictor.getRestrictedTypes().get(con);

			if (nodeType == null) {
				tlaModule.variables.add(con);
				isVariable = true;
			} else {
				if (nodeType instanceof EqualsNode) {
					tlaModule.definitions.add(new TLADefinition(con, nodeType
							.getExpression()));
				} else {
					this.tlaModule.variables.add(con);
					isVariable = true;
				}
			}
		}

		Node propertiesPerdicate = machineContext.getPropertiesMachineClause()
				.getPredicates();
		if (isVariable) {
			tlaModule.initPredicates.add(propertiesPerdicate);
		} else if (!tlaModule.assumes.contains(node)) {
			tlaModule.assumes.add(propertiesPerdicate);
		}
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		if (!tlaModule.initPredicates.contains(node.getPredicates())) {
			if (!tlaModule.assumes.contains(node.getPredicates())) {
				this.tlaModule.assumes.add(node.getPredicates());
			}
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
		this.configFile.invariant = true;
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {

		this.tlaModule.initPredicates.add(node.getSubstitutions());
		// node.getSubstitutions().apply(this);
	}

	@Override
	public void caseAOperationsMachineClause(AOperationsMachineClause node) {
		List<POperation> copy = new ArrayList<POperation>(node.getOperations());
		for (POperation e : copy) {
			this.tlaModule.operations.add(e);
		}

	}

	public TLAModule getTlaModule() {
		return tlaModule;
	}

	public ConfigFile getConfigFile() {
		return configFile;
	}

}
