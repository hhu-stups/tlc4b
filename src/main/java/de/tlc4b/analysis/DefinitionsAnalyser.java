package de.tlc4b.analysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
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
	private final Map<Node, Integer> deferredSetSize = new HashMap<>();

	public Integer getSize(Node node) {
		return deferredSetSize.get(node);
	}

	public DefinitionsAnalyser(MachineContext machineContext) {
		this.machineContext = machineContext;
		Set<Node> deferredSets = new HashSet<>(machineContext.getDeferredSets().values());

		findDefaultSizesInDefinitions();

		if (deferredSets.isEmpty())
			return;

		for (String string : machineContext.getDeferredSets().keySet()) {
			Node node = machineContext.getDefinitions().get("scope_" + string);
			if (node instanceof AExpressionDefinitionDefinition) {
				AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
				if (d.getRhs() instanceof AIntervalExpression) {
					AIntervalExpression interval = (AIntervalExpression) d.getRhs();
					int l_int = extractInteger(interval.getLeftBorder());
					int r_int = extractInteger(interval.getRightBorder());
					deferredSetSize.put(machineContext.getDeferredSets().get(string), r_int - l_int + 1);
				} else if (d.getRhs() instanceof AIntegerExpression) {
					deferredSetSize.put(machineContext.getDeferredSets().get(string), extractInteger(d.getRhs()));
				}
			}
		}
	}

	private void findDefaultSizesInDefinitions() {
		Node node = machineContext.getDefinitions().get("SET_PREF_DEFAULT_SETSIZE");
		if (null != node) {
			try {
				TLC4BGlobals.setDEFERRED_SET_SIZE(extractInteger(((AExpressionDefinitionDefinition) node).getRhs()));
			} catch (ClassCastException e) {
				throw new TranslationException("Unable to determine the default set size from definition SET_PREF_DEFAULT_SETSIZE: " + node.getEndPos(), e);
			}
		}

		node = machineContext.getDefinitions().get("SET_PREF_MAXINT");
		if (null != node) {
			try {
				TLC4BGlobals.setMAX_INT(extractInteger(((AExpressionDefinitionDefinition) node).getRhs()));
			} catch (ClassCastException e) {
				throw new TranslationException("Unable to determine MAXINT from definition SET_PREF_MAXINT: " + node.getEndPos(), e);
			}
		}

		node = machineContext.getDefinitions().get("SET_PREF_MININT");
		if (null != node) {
			try {
				AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
				int value;
				if (d.getRhs() instanceof AUnaryMinusExpression) {
					value = -extractInteger(((AUnaryMinusExpression) d.getRhs()).getExpression());
				} else {
					value = extractInteger(d.getRhs());
				}
				TLC4BGlobals.setMIN_INT(value);
			} catch (ClassCastException e) {
				throw new TranslationException("Unable to determine the MININT from definition SET_PREF_MININT: " + node.getEndPos(), e);
			}
		}
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		// TODO never reached
		Node ref_node = machineContext.getReferences().get(node);
		if (deferredSetSize.containsKey(ref_node)) {
			try {
				ACardExpression cardNode = (ACardExpression) node.parent();
				AEqualPredicate equalsNode = (AEqualPredicate) cardNode.parent();
				deferredSetSize.put(ref_node, extractInteger(equalsNode.getLeft() == cardNode ? equalsNode.getRight() : cardNode));
			} catch (ClassCastException e) {
			}
		}
	}

	private static int extractInteger(Node node) {
		return Integer.parseInt(((AIntegerExpression) node).getLiteral().getText());
	}
}
