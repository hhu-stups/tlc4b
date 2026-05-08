package de.tlc4b.analysis.transformation;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.util.Utils;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class OperationCallInjector extends DepthFirstAdapter {

	private final Map<String, PExpression> arguments = new HashMap<>(); // identifier -> expression

	private OperationCallInjector(AOperation operation, List<PExpression> arguments) {
		if (operation.getParameters().size() != arguments.size()) {
			throw new IllegalArgumentException("Number of arguments does not match number of operation parameters.");
		}
		List<PExpression> parameters = operation.getParameters();
		for (int i = 0; i < arguments.size(); i++) {
			this.arguments.put(Utils.getAIdentifierAsString((AIdentifierExpression) parameters.get(i)),
					arguments.get(i));
		}
		operation.apply(this);
	}

	public static void injectArguments(AOperation operation, List<PExpression> arguments) {
		new OperationCallInjector(operation, arguments);
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (arguments.containsKey(Utils.getAIdentifierAsString(node))) {
			node.replaceBy(arguments.get(Utils.getAIdentifierAsString(node)).clone());
		}
	}
}
