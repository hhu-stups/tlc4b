package de.tlc4b.util;

import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.*;
import de.hhu.stups.sablecc.patch.SourcePosition;

public class UtilMethods {

	public static AIdentifierExpression createAIdentifierExpression(String name) {
		TIdentifierLiteral literal = new TIdentifierLiteral(name);
		ArrayList<TIdentifierLiteral> idList = new ArrayList<>();
		idList.add(literal);
		return new AIdentifierExpression(idList);
	}

	public static AIdentifierExpression getIdentifierExpression(PExpression e) {
		AIdentifierExpression identifier;
		if (e instanceof ADescriptionExpression) {
			PExpression desc = ((ADescriptionExpression) e).getExpression();
			if (desc instanceof AIdentifierExpression) {
				identifier = (AIdentifierExpression) desc;
			} else {
				throw new IllegalStateException("Unexpected expression type: " + e);
			}
		} else if (e instanceof AIdentifierExpression) {
			identifier = (AIdentifierExpression) e;
		} else {
			throw new IllegalStateException("Unexpected expression type: " + e);
		}
		return identifier;
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
