package de.tlc4b.analysis.typerestriction;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;

public class IdentifierDependencies extends DepthFirstAdapter {

	private final MachineContext machineContext;
	private final Map<Node, Set<Node>> usedIdentifier;

	public IdentifierDependencies(MachineContext machineContext) {
		this.machineContext = machineContext;
		this.usedIdentifier = new HashMap<>();
	}

	public boolean containsIdentifier(Node node, Set<Node> set) {
		node.apply(this);
		return set.stream().anyMatch(usedIdentifier.get(node)::contains);
	}
	
	public void defaultOut(Node node) {
		setSetToNode(node, usedIdentifier.get(node));
		setSetToNode(node.parent(), usedIdentifier.get(node));
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node refNode = machineContext.getReferenceNode(node);
		if (refNode == null)
			refNode = node;
		setSetToNode(node, Collections.singleton(refNode));
		defaultOut(node);
	}

	private void setSetToNode(Node node, Set<Node> set) {
		Set<Node> oldSet = usedIdentifier.computeIfAbsent(node, k -> new HashSet<>());
		if (set != null)
			oldSet.addAll(set);
		usedIdentifier.put(node, oldSet);
	}
}
