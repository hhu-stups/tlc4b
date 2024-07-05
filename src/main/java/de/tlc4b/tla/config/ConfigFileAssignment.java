package de.tlc4b.tla.config;

import java.util.ArrayList;
import java.util.List;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.tlc4b.analysis.Renamer;

public abstract class ConfigFileAssignment {

	public abstract String getString(Renamer renamer);
	
	public String getIdentifier(AIdentifierExpression node) {
		StringBuilder res = new StringBuilder();
		
		List<TIdentifierLiteral> copy = new ArrayList<>(
				node.getIdentifier());
		for (TIdentifierLiteral e : copy) {
			res.append(e.getText());
		}
		return res.toString();
	}
	
}
