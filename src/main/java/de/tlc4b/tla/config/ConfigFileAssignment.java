package de.tlc4b.tla.config;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.tlc4b.analysis.Renamer;

public abstract class ConfigFileAssignment {

	public abstract String getString(Renamer renamer);
	
	public String getIdentifier(AIdentifierExpression node) {
		return node.getIdentifier().stream()
				.map(TIdentifierLiteral::getText)
				.collect(Collectors.joining());
	}
	
}
