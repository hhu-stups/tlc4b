package de.tlc4b.analysis.unchangedvariables;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;

public class InvariantPreservationAnalysis extends DepthFirstAdapter {

	private final MachineContext machineContext;
	private final Map<Node, Set<Node>> preservingOperations = new HashMap<>(); // results
	private Set<Node> usedVariables; //temp

	public List<Node> getPreservingOperations(Node invariant) {
		return new ArrayList<>(preservingOperations.get(invariant));
	}

	public InvariantPreservationAnalysis(MachineContext machineContext, List<Node> invariants,
	                                     UnchangedVariablesFinder unchangedFinder) {
		this.machineContext = machineContext;

		for (Node inv : invariants) {
			usedVariables = new HashSet<>();
			inv.apply(this);
			Set<Node> preservingOperations = new HashSet<>();
			for (Node op : machineContext.getOperations().values()) {
				if (Collections.disjoint(usedVariables, unchangedFinder.getAssignedVariables(op))) {
					preservingOperations.add(op);
				}
			}
			this.preservingOperations.put(inv, preservingOperations);
		}
	}

	public void inAIdentifierExpression(AIdentifierExpression node) {
		Node identifier = machineContext.getReferenceNode(node);
		if (machineContext.getVariables().containsValue(identifier)) {
			usedVariables.add(identifier);
		}
	}

}
