package de.b2tla.analysis.unchangedvariables;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.b2tla.analysis.MachineContext;
import de.b2tla.exceptions.SubstitutionException;
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
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASelectWhenSubstitution;
import de.be4.classicalb.core.parser.node.ASkipSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSubstitution;

/**
 * 
 * This class is a tree walker which searches for all assigned variables in a
 * branch of a operation body. The algorithm works in a bottom up style. The
 * {@link assignedVariablesTable} will finally contain all assigned variables
 * for a node. For example a {@link AParallelSubstitution} node will get a list
 * of all assigned variables of its children. Operation output parameter are
 * handled as variables.
 * 
 */

public class AssignedVariablesFinder extends DepthFirstAdapter {
	private final Hashtable<Node, HashSet<Node>> assignedVariablesTable;
	private final MachineContext machineContext;

	public AssignedVariablesFinder(MachineContext machineContext) {
		this.assignedVariablesTable = new Hashtable<Node, HashSet<Node>>();
		this.machineContext = machineContext;
		machineContext.getTree().apply(this);

	}

	public Hashtable<Node, HashSet<Node>> getAssignedVariablesTable() {
		return assignedVariablesTable;
	}

	private HashSet<Node> getVariableList(Node node) {
		return assignedVariablesTable.get(node);
	}

	@Override
	public void defaultOut(final Node node) {
		/*
		 * This case is important if the parent node is not visited by the
		 * visitor. The assigned variables are transfered up in the tree. e.g.
		 * if the parent node is a block substitution, the assigned variables
		 * are transfered to parent of the block substitution
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
		HashSet<Node> allVariables = new HashSet<Node>(machineContext
				.getVariables().values());
		HashSet<Node> foundVariables = new HashSet<Node>(
				getVariableList(node.getSubstitutions()));

		if (allVariables.retainAll(foundVariables)) {
			HashSet<Node> missingVariables = new HashSet<Node>(machineContext
					.getVariables().values());
			missingVariables.removeAll(allVariables);
			throw new SubstitutionException(
					"Initialisation Error: Missing assignment for variable(s): "
							+ missingVariables);
		}

	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		HashSet<Node> list = new HashSet<Node>();
		for (PExpression e : copy) {
			Node identifier = machineContext.getReferences().get(e);
			list.add(identifier);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		HashSet<Node> list = new HashSet<Node>();
		for (PExpression e : copy) {
			if (e instanceof AIdentifierExpression) {
				Node identifier = machineContext.getReferences().get(e);
				list.add(identifier);
			} else {
				AFunctionExpression func = (AFunctionExpression) e;
				Node identifier = machineContext.getReferences().get(
						func.getIdentifier());
				list.add(identifier);
			}
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseABecomesElementOfSubstitution(
			ABecomesElementOfSubstitution node) {

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		HashSet<Node> list = new HashSet<Node>();
		for (PExpression e : copy) {
			Node identifier = machineContext.getReferences().get(e);
			list.add(identifier);
		}
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		HashSet<Node> list = new HashSet<Node>();
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
		assignedVariablesTable.put(node,
				getVariableList(node.getSubstitution()));
		defaultOut(node);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		node.getThen().apply(this);
		list.addAll(getVariableList(node.getThen()));

		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
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
		HashSet<Node> list = new HashSet<Node>();
		node.getThenSubstitution().apply(this);
		list.addAll(getVariableList(node.getThenSubstitution()));

		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		HashSet<Node> list = new HashSet<Node>();
		for (PSubstitution e : copy) {
			HashSet<Node> listOfe = getVariableList(e);
			HashSet<Node> temp = new HashSet<Node>(list);
			temp.retainAll(listOfe);
			if (temp.size() > 0) {
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
		HashSet<Node> list = new HashSet<Node>();
		node.getThen().apply(this);
		list.addAll(getVariableList(node.getThen()));
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getWhenSubstitutions());
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
		assignedVariablesTable.put(node,
				getVariableList(node.getSubstitution()));
		assignedVariablesTable.put(node.parent(),
				getVariableList(node.getSubstitution()));
	}

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
		List<PDefinition> copy = new ArrayList<PDefinition>(
				node.getDefinitions());
		for (PDefinition e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		Node refNode = machineContext.getReferences().get(node);
		HashSet<Node> assignedVariables = assignedVariablesTable.get(refNode);
		assignedVariablesTable.put(node, assignedVariables);
		assignedVariablesTable.put(node.parent(), assignedVariables);
	}

	@Override
	public void caseASkipSubstitution(ASkipSubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		assignedVariablesTable.put(node, list);
		defaultOut(node);
	}
}