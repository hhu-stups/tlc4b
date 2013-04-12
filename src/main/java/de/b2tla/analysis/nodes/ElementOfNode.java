package de.b2tla.analysis.nodes;

import de.be4.classicalb.core.parser.node.PExpression;

public class ElementOfNode implements NodeType {
	PExpression expr;

	public ElementOfNode(PExpression expr) {
		this.expr = expr;
	}

	public PExpression getExpression() {
		return expr;
	}
}
