package de.b2tla.tla.config;

import java.util.ArrayList;
import java.util.List;

import de.b2tla.analysis.Renamer;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public abstract class ConfigFileAssignment {

	public abstract String getString(Renamer renamer);
	
	public String getIdentifier(AIdentifierExpression node) {
		String res = "";
		List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
				node.getIdentifier());
		for (TIdentifierLiteral e : copy) {
			res += e.getText();
		}
		return res;
	}
	
}
