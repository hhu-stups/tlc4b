package de.tlc4b.ltl;

import de.be4.classicalb.core.parser.node.Node;

import java.util.Map;

public class LTLBPredicate {
	private final Map<String, Node> identifierMap;
	private final Node predicate;

	public LTLBPredicate(Map<String, Node> identifierMap, Node predicate) {
		this.identifierMap = identifierMap;
		this.predicate = predicate;
	}

	public Node getBFormula(){
		return predicate;
	}

	public Map<String, Node> getIdentifierMap() {
		return identifierMap;
	}
}
