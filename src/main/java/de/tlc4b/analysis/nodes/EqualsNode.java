package de.tlc4b.analysis.nodes;

import de.be4.classicalb.core.parser.node.PExpression;

public class EqualsNode implements NodeType {
	PExpression expr;

	public EqualsNode(PExpression subExpr) {
		this.expr = subExpr;
	}

	public PExpression getExpression() {
		return expr;
	}
}
