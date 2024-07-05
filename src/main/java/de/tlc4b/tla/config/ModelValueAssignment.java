package de.tlc4b.tla.config;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.Renamer;

public class ModelValueAssignment extends ConfigFileAssignment{
	private final Node node;
	
	public ModelValueAssignment(Node node){
		this.node = node;
	}

	public String getString(Renamer renamer) {
		AIdentifierExpression id = (AIdentifierExpression) node;
		getIdentifier(id);
		String conString = renamer.getNameOfRef(id);
		return conString+ " = "+ conString +"\n";
	}
	
}
