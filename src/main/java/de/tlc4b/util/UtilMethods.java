package de.tlc4b.util;

import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class UtilMethods {

	public static AIdentifierExpression createAIdentifierExpression(String name) {
		TIdentifierLiteral literal = new TIdentifierLiteral(name);
		ArrayList<TIdentifierLiteral> idList = new ArrayList<TIdentifierLiteral>();
		idList.add(literal);
		AIdentifierExpression id = new AIdentifierExpression(idList);
		return id;
	}
	
}
