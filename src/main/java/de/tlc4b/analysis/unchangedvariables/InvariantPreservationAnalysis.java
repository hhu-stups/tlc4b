package de.tlc4b.analysis.unchangedvariables;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;

public class InvariantPreservationAnalysis extends DepthFirstAdapter {
	protected final Hashtable<Node, HashSet<Node>> foundVariablesTable;
	private final MachineContext machineContext;

	// results
	private final Hashtable<Node, HashSet<Node>> preservingOperationsTable;

	// temp
	private HashSet<Node> foundVariables;

	public ArrayList<Node> getPreservingOperations(Node invariant) {
		return new ArrayList<>(preservingOperationsTable.get(invariant));
	}

	public InvariantPreservationAnalysis(MachineContext machineContext,
			ArrayList<Node> invariants, UnchangedVariablesFinder unchangedFinder) {
		this.foundVariablesTable = new Hashtable<>();
		this.machineContext = machineContext;

		this.preservingOperationsTable = new Hashtable<>();

		for (Node inv : invariants) {
			foundVariables = new HashSet<>();
			inv.apply(this);
			foundVariablesTable.put(inv, foundVariables);
		}

		for (Node inv : invariants) {
			HashSet<Node> preservingOperations = new HashSet<>();
			HashSet<Node> usedVariables = foundVariablesTable.get(inv);
			for (Node op : machineContext.getOperations().values()) {
				HashSet<Node> assignedVariables = unchangedFinder
						.getAssignedVariables(op);
				HashSet<Node> temp = new HashSet<>(usedVariables);
				temp.retainAll(assignedVariables);
				if (temp.isEmpty()) {
					preservingOperations.add(op);
				}
			}
			preservingOperationsTable.put(inv, preservingOperations);
		}
	}

	public void inAIdentifierExpression(AIdentifierExpression node) {
		Node identifier = machineContext.getReferenceNode(node);
		if (machineContext.getVariables().containsValue(identifier)) {
			foundVariables.add(identifier);
		}
	}

}
