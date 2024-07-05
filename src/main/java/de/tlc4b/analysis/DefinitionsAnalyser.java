package de.tlc4b.analysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.exceptions.TranslationException;

/**
 * @author hansen In this class we search for preferences set in the definitions
 *         clause, e.g. minint or maxint.
 */

public class DefinitionsAnalyser extends DepthFirstAdapter {
	private final MachineContext machineContext;
	private final HashMap<Node, Integer> deferredSetSizeTable;

	public Integer getSize(Node node) {
		return deferredSetSizeTable.get(node);
	}

	public DefinitionsAnalyser(MachineContext machineContext) {
		this.machineContext = machineContext;
		deferredSetSizeTable = new HashMap<>();
		HashSet<Node> deferredSets = new HashSet<>(machineContext.getDeferredSets().values());

		findDefaultSizesInDefinitions();

		if (deferredSets.isEmpty())
			return;

		Set<String> strings = machineContext.getDeferredSets().keySet();
		for (String string : strings) {
			String s = "scope_" + string;
			Node node = machineContext.getDefinitions().get(s);
			if (null != node) {
				try {
					AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
					AIntervalExpression interval = (AIntervalExpression) d
							.getRhs();
					AIntegerExpression left = (AIntegerExpression) interval
							.getLeftBorder();
					AIntegerExpression right = (AIntegerExpression) interval
							.getRightBorder();
					int l_int = Integer.parseInt(left.getLiteral().getText());
					int r_int = Integer.parseInt(right.getLiteral().getText());
					int size = r_int - l_int + 1;
					deferredSetSizeTable.put(machineContext.getDeferredSets()
							.get(string), size);
				} catch (ClassCastException e) {
				}
				try {
					AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
					AIntegerExpression sizeExpr = (AIntegerExpression) d
							.getRhs();
					int size = Integer
							.parseInt(sizeExpr.getLiteral().getText());
					deferredSetSizeTable.put(machineContext.getDeferredSets()
							.get(string), size);
				} catch (ClassCastException e) {
				}

			}
		}
	}

	private void findDefaultSizesInDefinitions() {
		Node node = machineContext.getDefinitions().get(
				"SET_PREF_DEFAULT_SETSIZE");
		if (null != node) {
			try {
				AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
				AIntegerExpression sizeExpr = (AIntegerExpression) d.getRhs();
				int value = Integer.parseInt(sizeExpr.getLiteral().getText());
				TLC4BGlobals.setDEFERRED_SET_SIZE(value);
			} catch (ClassCastException e) {
				throw new TranslationException(
						"Unable to determine the default set size from definition SET_PREF_DEFAULT_SETSIZE: "
								+ node.getEndPos());
			}
		}

		node = machineContext.getDefinitions().get("SET_PREF_MAXINT");
		if (null != node) {
			try {
				AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
				AIntegerExpression sizeExpr = (AIntegerExpression) d.getRhs();
				int value = Integer.parseInt(sizeExpr.getLiteral().getText());
				TLC4BGlobals.setMAX_INT(value);
			} catch (ClassCastException e) {
				throw new TranslationException(
						"Unable to determine MAXINT from definition SET_PREF_MAXINT: "
								+ node.getEndPos());
			}
		}

		node = machineContext.getDefinitions().get("SET_PREF_MININT");
		if (null != node) {
			try {
				AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
				AIntegerExpression sizeExpr;
				int value;
				if (d.getRhs() instanceof AUnaryMinusExpression) {
					AUnaryMinusExpression minus = (AUnaryMinusExpression) d
							.getRhs();
					sizeExpr = (AIntegerExpression) minus.getExpression();
					value = -Integer.parseInt(sizeExpr.getLiteral().getText());
				} else {
					sizeExpr = (AIntegerExpression) d.getRhs();
					value = Integer.parseInt(sizeExpr.getLiteral().getText());
				}
				TLC4BGlobals.setMIN_INT(value);
			} catch (ClassCastException e) {
				throw new TranslationException(
						"Unable to determine the MININT from definition SET_PREF_MININT: " + node.getEndPos());
			}
		}
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		// TODO never reached
		Node ref_node = machineContext.getReferences().get(node);
		if (deferredSetSizeTable.containsKey(ref_node)) {
			try {
				ACardExpression cardNode = (ACardExpression) node.parent();
				AEqualPredicate equalsNode = (AEqualPredicate) cardNode
						.parent();
				AIntegerExpression integer;
				if (equalsNode.getLeft() == cardNode) {
					integer = (AIntegerExpression) equalsNode.getRight();
				} else {
					integer = (AIntegerExpression) equalsNode.getLeft();
				}
				String intString = integer.getLiteral().getText();
				deferredSetSizeTable.put(ref_node, Integer.parseInt(intString));
			} catch (ClassCastException e) {
			}

		}
	}
}
