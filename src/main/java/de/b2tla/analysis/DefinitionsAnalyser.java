package de.b2tla.analysis;

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
import de.be4.classicalb.core.parser.node.Node;

public class DefinitionsAnalyser extends DepthFirstAdapter{
	private MachineContext machineContext;
	private HashMap<Node, Integer> deferredSetSizeTable;

	public Integer getSize(Node node) {
		return deferredSetSizeTable.get(node);
	}

	public DefinitionsAnalyser(MachineContext machineContext) {
		this.machineContext = machineContext;
		deferredSetSizeTable = new HashMap<Node, Integer>();
		HashSet<Node> deferredSets = new HashSet<Node>(machineContext
				.getDeferredSets().values());
		if (deferredSets.size() == 0)
			return;

		Set<String> strings = machineContext.getDeferredSets().keySet();
		for (String string : strings) {
			String s = "scope_"+ string;
			Node node = machineContext.getDefinitions().get(s);
			if(null != node){
				try {
					AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
					AIntervalExpression interval = (AIntervalExpression) d.getRhs();
					AIntegerExpression left = (AIntegerExpression) interval.getLeftBorder();
					AIntegerExpression right = (AIntegerExpression) interval.getRightBorder();
					int l_int = Integer.parseInt(left.getLiteral().getText());
					int r_int = Integer.parseInt(right.getLiteral().getText());
					int size = r_int - l_int + 1;
					deferredSetSizeTable.put(machineContext.getDeferredSets().get(string), size);
				} catch (ClassCastException e) {
				}
				try {
					AExpressionDefinitionDefinition d = (AExpressionDefinitionDefinition) node;
					AIntegerExpression sizeExpr = (AIntegerExpression) d.getRhs();
					int size = Integer.parseInt(sizeExpr.getLiteral().getText());
					deferredSetSizeTable.put(machineContext.getDeferredSets().get(string), size);
				} catch (ClassCastException e) {
				}
				
				
			}
		}
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node ref_node = machineContext.getReferences().get(node);
		if(deferredSetSizeTable.containsKey(ref_node)){
			try {
				ACardExpression cardNode = (ACardExpression) node.parent();
				AEqualPredicate equalsNode = (AEqualPredicate)	cardNode.parent();
				AIntegerExpression integer;
				if(equalsNode.getLeft() == cardNode){
					integer = (AIntegerExpression) equalsNode.getRight();
				}else{
					integer = (AIntegerExpression) equalsNode.getLeft();
				}
				String intString = integer.getLiteral().getText();
				deferredSetSizeTable.put(ref_node, Integer.parseInt(intString));
			} catch (ClassCastException e) {
				return;
			}
				
		}
	}
}
