package b2tla.analysis.nodes;

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
