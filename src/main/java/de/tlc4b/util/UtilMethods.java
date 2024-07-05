package de.tlc4b.util;

import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.hhu.stups.sablecc.patch.SourcePosition;

public class UtilMethods {

	public static AIdentifierExpression createAIdentifierExpression(String name) {
		TIdentifierLiteral literal = new TIdentifierLiteral(name);
		ArrayList<TIdentifierLiteral> idList = new ArrayList<>();
		idList.add(literal);
		return new AIdentifierExpression(idList);
	}

	public static String getPositionAsString(Node node) {
		StringBuilder sb = new StringBuilder();
		SourcePosition startPos = node.getStartPos();
		SourcePosition endPos = node.getEndPos();
		if (startPos == null) {
			sb.append("### Unknown position.");
		} else {
			sb.append("### Line ");
			sb.append(startPos.getLine());
			sb.append(", Column ");
			sb.append(endPos.getPos());
		}

		return sb.toString();
	}

}
