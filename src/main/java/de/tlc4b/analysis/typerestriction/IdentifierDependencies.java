package de.tlc4b.analysis.typerestriction;

import java.util.HashMap;
import java.util.HashSet;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;

public class IdentifierDependencies extends DepthFirstAdapter {

	private final MachineContext machineContext;
	private final HashMap<Node, HashSet<Node>> usedIdentifier;

	public IdentifierDependencies(MachineContext machineContext) {
		this.machineContext = machineContext;

		this.usedIdentifier = new HashMap<Node, HashSet<Node>>();

	}

	public boolean containsIdentifier(Node node, HashSet<Node> list){
		//if(!usedIdentifier.containsKey(node)){
			node.apply(this);
		//}
		HashSet<Node> set = usedIdentifier.get(node);
		for (Node id : list) {
			if(set.contains(id))
				return true;
		}
		return false;
	}
	
	public void defaultOut(Node node) {
		setSetToNode(node, usedIdentifier.get(node));
		setSetToNode(node.parent(), usedIdentifier.get(node));
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node refNode = machineContext.getReferences().get(node);
		if(refNode == null)
			refNode = node;
		HashSet<Node> set = new HashSet<Node>();
		set.add(refNode);
		setSetToNode(node, set);

		defaultOut(node);
	}

	private void setSetToNode(Node node, HashSet<Node> set) {
		HashSet<Node> oldSet = usedIdentifier.get(node);
		if (oldSet == null) {
			oldSet = new HashSet<Node>();
		} 
		if (set != null) {
			oldSet.addAll(set);
		}
		usedIdentifier.put(node, oldSet);
	}
}
