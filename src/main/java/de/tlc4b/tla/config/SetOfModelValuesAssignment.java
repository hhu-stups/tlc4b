package de.tlc4b.tla.config;

import java.util.List;

import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.Renamer;

/**
 * 
 * This class represents an assignment in the configuration file. The left side
 * of the assignment is a constant and the right side a set of model values.
 * E.g. k = {k1, k2, k3}
 */

public class SetOfModelValuesAssignment extends ConfigFileAssignment {
	private final Node node;
	private final int size;

	public SetOfModelValuesAssignment(Node node, Integer size) {
		this.node = node;
		if (size == null) {
			this.size = TLC4BGlobals.getDEFERRED_SET_SIZE();
		} else {
			this.size = size;
		}

	}

	public String getString(Renamer renamer) {
		StringBuilder res = new StringBuilder();

		StringBuilder conString;
		if (node instanceof ADeferredSetSet) {
			conString = new StringBuilder();
			List<TIdentifierLiteral> copy = ((ADeferredSetSet) node)
					.getIdentifier();
			for (TIdentifierLiteral e : copy) {
				conString.append(e.getText());
			}
			conString = new StringBuilder(renamer.getName(node));
		} else {
			AIdentifierExpression id = (AIdentifierExpression) node;
			conString = new StringBuilder(getIdentifier(id));
		}

		res.append(conString).append(" = {");
		for (int j = 1; j < size + 1; j++) {
			res.append(conString).append(j);
			if (j < size) {
				res.append(",");
			}
		}
		res.append("}\n");

		return res.toString();
	}

}
