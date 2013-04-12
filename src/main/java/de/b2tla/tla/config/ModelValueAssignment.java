package de.b2tla.tla.config;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;

public class ModelValueAssignment extends ConfigFileAssignment{
	private Node node;
	
	public ModelValueAssignment(Node node){
		this.node = node;
	}

	public String getString() {
		AIdentifierExpression id = (AIdentifierExpression) node;
		String conString = getIdentifier(id);
		return conString+ " = "+ conString +"\n";
	}
	
}
