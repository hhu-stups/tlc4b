package de.tlc4b.analysis.unchangedvariables;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesElementOfSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.ABlockSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceOrSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIfElsifSubstitution;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AParallelSubstitution;
import de.be4.classicalb.core.parser.node.ARecordFieldExpression;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASelectWhenSubstitution;
import de.be4.classicalb.core.parser.node.ASkipSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.exceptions.NotSupportedException;
import de.tlc4b.exceptions.SubstitutionException;

/**
 * 
 * This class is a tree walker which searches for all assigned variables in a
 * branch of an operation body. The algorithm works in a bottom up style. The
 * {@link assignedVariablesTable} will finally contain all assigned variables
 * for a node. For example a {@link AParallelSubstitution} node will get a list
 * of all assigned variables of its children. Operation output parameter are
 * handled as variables.
 * 
 */

public class AssignedVariablesFinder extends DepthFirstAdapter {
	protected final Hashtable<Node, HashSet<Node>> assignedVariablesTable;
	private final MachineContext machineContext;

	public AssignedVariablesFinder(MachineContext machineContext) {
		this.assignedVariablesTable = new Hashtable<>();
		this.machineContext = machineContext;
		machineContext.getStartNode().apply(this);

	}

	protected Hashtable<Node, HashSet<Node>> getAssignedVariablesTable() {
		return assignedVariablesTable;
	}

	private HashSet<Node> getVariableList(Node node) {
		return assignedVariablesTable.get(node);
	}

	@Override
	public void defaultOut(final Node node) {
		/*
		 * This case is important if the parent node is not visited by the
		 * visitor. The assigned variables are transferred up in the tree. e.g.
		 * if the parent node is a block substitution, the assigned variables
		 * are transferred to parent of the block substitution
		 */
		HashSet<Node> assignedVariables = assignedVariablesTable.get(node);
		if (null != assignedVariables) {
			assignedVariablesTable.put(node.parent(), assignedVariables);
		}
	}

	@Override
	public void caseABlockSubstitution(ABlockSubstitution node) {
		inABlockSubstitution(node);
		if (node.getSubstitution() != null) {
			node.getSubstitution().apply(this);
		}
		outABlockSubstitution(node);
	}

	@Override
	public void caseAOperation(AOperation node) {
		node.getOperationBody().apply(this);
		assignedVariablesTable.put(node,
				getVariableList(node.getOperationBody()));
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		// first visit the sub node
		node.getSubstitutions().apply(this);
		assignedVariablesTable.put(node,
				getVariableList(node.getSubstitutions()));

		/*
		 * In the INITIALISATION clause all variables must be assigned.
		 */
		HashSet<Node> allVariables = new HashSet<>(machineContext.getVariables().values());
		HashSet<Node> foundVariables = new HashSet<>(getVariableList(node.getSubstitutions()));

		if (allVariables.retainAll(foundVariables)) {
			HashSet<Node> missingVariables = new HashSet<>(machineContext.getVariables().values());
			missingVariables.removeAll(allVariables);
			throw new SubstitutionException(
					"Initialisation Error: Missing assignment for variable(s): "
							+ missingVariables);
		}

	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		HashSet<Node> list = new HashSet<>();
		for (PExpression e : copy) {
			Node identifier = machineContext.getReferenceNode(e);
			list.add(identifier);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getLhsExpression());
		HashSet<Node> list = new HashSet<>();
		for (PExpression e : copy) {
			Node assigned = getAssignedVariable(e);
			Node identifier = machineContext.getReferenceNode(assigned);
			list.add(identifier);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	private PExpression getAssignedVariable(PExpression e) {
		if (e instanceof AIdentifierExpression) {
			return e;
		} else if (e instanceof AFunctionExpression) {
			return getAssignedVariable(((AFunctionExpression) e).getIdentifier());
		} else if (e instanceof ARecordFieldExpression) {
			return getAssignedVariable(((ARecordFieldExpression) e).getRecord());
		} else {
			throw new NotSupportedException("Unknown assignment lhs: " + e);
		}
	}

	@Override
	public void caseABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		HashSet<Node> list = new HashSet<>();
		for (PExpression e : copy) {
			Node identifier = machineContext.getReferenceNode(e);
			list.add(identifier);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<>(node.getSubstitutions());
		HashSet<Node> list = new HashSet<>();
		for (PSubstitution e : copy) {
			e.apply(this);
			list.addAll(getVariableList(e));
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAChoiceOrSubstitution(AChoiceOrSubstitution node) {
		node.getSubstitution().apply(this);
		assignedVariablesTable.put(node, getVariableList(node.getSubstitution()));
		defaultOut(node);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		node.getThen().apply(this);
		HashSet<Node> list = new HashSet<>(getVariableList(node.getThen()));

		List<PSubstitution> copy = new ArrayList<>(node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
			list.addAll(getVariableList(e));
		}
		if (node.getElse() != null) {
			node.getElse().apply(this);
			list.addAll(getVariableList(node.getElse()));
		}

		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAIfElsifSubstitution(AIfElsifSubstitution node) {
		node.getThenSubstitution().apply(this);
		HashSet<Node> list = new HashSet<>(getVariableList(node.getThenSubstitution()));

		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		List<PSubstitution> copy = new ArrayList<>(node.getSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		HashSet<Node> list = new HashSet<>();
		for (PSubstitution e : copy) {
			HashSet<Node> listOfe = getVariableList(e);
			HashSet<Node> temp = new HashSet<>(list);
			temp.retainAll(listOfe);
			if (!temp.isEmpty()) {
				throw new SubstitutionException("The variable(s) " + temp
						+ " are assigned twice");
			}
			list.addAll(listOfe);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseASelectSubstitution(ASelectSubstitution node) {
		node.getThen().apply(this);
		HashSet<Node> list = new HashSet<>(getVariableList(node.getThen()));
		List<PSubstitution> copy = new ArrayList<>(node.getWhenSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
			list.addAll(getVariableList(e));
		}
		if (node.getElse() != null) {
			node.getElse().apply(this);
			list.addAll(getVariableList(node.getElse()));
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseASelectWhenSubstitution(ASelectWhenSubstitution node) {
		node.getSubstitution().apply(this);
		assignedVariablesTable.put(node, getVariableList(node.getSubstitution()));
		assignedVariablesTable.put(node.parent(), getVariableList(node.getSubstitution()));
	}

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
		List<PDefinition> copy = new ArrayList<>(node.getDefinitions());
		for (PDefinition e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		Node refNode = machineContext.getReferenceNode(node);
		HashSet<Node> assignedVariables = assignedVariablesTable.get(refNode);
		assignedVariablesTable.put(node, assignedVariables);
		assignedVariablesTable.put(node.parent(), assignedVariables);
	}

	@Override
	public void caseASkipSubstitution(ASkipSubstitution node) {
		HashSet<Node> list = new HashSet<>();
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}
}