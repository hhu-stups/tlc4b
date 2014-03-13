package de.tlc4b.analysis.nodes;

import de.be4.classicalb.core.parser.node.PExpression;

public class SubsetNode implements NodeType{
	PExpression expr;
	
	public SubsetNode(PExpression expr){
		this.expr = expr;
	}
	
	public PExpression getExpression() {
		return expr;
	}

}
