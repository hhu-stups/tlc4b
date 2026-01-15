package de.tlc4b.tla.config;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
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
		this.size = size == null ? TLC4BGlobals.getDEFERRED_SET_SIZE() : size;
	}

	public String getString(Renamer renamer) {
		String conString;
		if (node instanceof ADeferredSetSet) {
			conString = renamer.getName(node);
		} else {
			conString = getIdentifier((AIdentifierExpression) node);
		}

		return conString + " = {" +
				IntStream.rangeClosed(1, size).mapToObj(j -> conString + j).collect(Collectors.joining(",")) +
				"}\n";
	}
}
