package de.b2tla.tla.config;

import java.util.List;

import de.b2tla.B2TLAGlobals;
import de.b2tla.analysis.Renamer;
import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
/**
 * 
 * This class represents an assignment in the configuration file.
 * The left side of the assignment is a constant and the right side a set of model values.
 * E.g. k = {k1, k2, k3}
 */

public class SetOfModelValuesAssignment extends ConfigFileAssignment{
	private Node node;
	private int size;

	public SetOfModelValuesAssignment(Node node, Integer size) {
		this.node = node;
		if(size == null){
			this.size = B2TLAGlobals.getDEFERRED_SET_SIZE();
		}else{
			this.size = size;
		}
		
	}

	public String getString(Renamer renamer) {
		String res = "";
		String conString;
		if (node instanceof ADeferredSetSet) {
			conString = "";
			List<TIdentifierLiteral> copy = ((ADeferredSetSet) node)
					.getIdentifier();
			for (TIdentifierLiteral e : copy) {
				conString += e.getText();
			}
			conString = renamer.getName(node);
		}else{
			AIdentifierExpression id = (AIdentifierExpression) node;
			conString = getIdentifier(id);
		}
		
		res += conString + " = {";
		for (int j = 1; j < size + 1; j++) {
			res += conString + j;
			if (j < size) {
				res += ", ";
			}
		}
		res += "}\n";
		
		return res;
	}
	
	
}
