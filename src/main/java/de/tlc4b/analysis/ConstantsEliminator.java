package de.tlc4b.analysis;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;

public class ConstantsEliminator extends DepthFirstAdapter {

	private final Hashtable<Node, HashSet<Node>> dependsOnIdentifierTable;
	private final MachineContext machineContext;
	private ValuesOfIdentifierFinder valuesOfConstantsFinder;
	private final HashMap<Node, Integer> integerValueTable;
	
	private LinkedHashMap<Node, Node> valueOfIdentifier;

	public Node getValueOfConstant(Node con) {
		return valueOfIdentifier.get(con);
	}

	public LinkedHashMap<Node, Node> getValueOfIdentifierMap() {
		return valueOfIdentifier;
	}

	public Integer getIntValue(Node node) {
		return integerValueTable.get(node);
	}

	public ConstantsEliminator(MachineContext machineContext) {
		this.dependsOnIdentifierTable = new Hashtable<>();
		this.integerValueTable = new HashMap<>();
		this.machineContext = machineContext;
	}

	public void start() {
		ConstantsInTreeFinder constantInTreeFinder = new ConstantsInTreeFinder();

		APropertiesMachineClause properties = machineContext
				.getPropertiesMachineClause();
		if (null != properties) {
			properties.apply(constantInTreeFinder);
		}

		AConstraintsMachineClause constraints = machineContext
				.getConstraintMachineClause();
		if (null != constraints) {
			constraints.apply(constantInTreeFinder);
		}

		this.valuesOfConstantsFinder = new ValuesOfIdentifierFinder();

		this.valueOfIdentifier = new LinkedHashMap<>();

		// creating a new list of the constants, because constants will be
		// removed from the original list
		LinkedList<Node> oldConstants = new LinkedList<>(machineContext.getConstantArrayList());
		if (!oldConstants.isEmpty()) {
			evalIdentifier(oldConstants);
		}

		// TODO adapting the elimination of constants to scalar parameters
		// evalIdentifier(machineContext.getScalarParameter().values());
	}

	private void evalIdentifier(Collection<Node> ids) {
		LinkedList<PDefinition> defsList = new LinkedList<>();
		boolean newRun = true;
		while (newRun) {
			newRun = false;
			for (Node node : ids) {
				AIdentifierExpression id = (AIdentifierExpression) node;
				if (valueOfIdentifier.containsKey(id))
					continue;
				HashSet<Node> idValues = valuesOfConstantsFinder.valuesOfIdentifierTable.get(id);
				for (Node val : idValues) {
					HashSet<Node> idsInVal = dependsOnIdentifierTable.get(val);
					if (idsInVal.isEmpty()) {
						// remove constants assignment of the properties clause
						removeAssignmentInPropertiesClause(val);
						removeConstant(id);
						AExpressionDefinitionDefinition def = new AExpressionDefinitionDefinition(
							id.getIdentifier().get(0).clone(),
							new LinkedList<>(),
							(PExpression) val);
						machineContext.getReferences().put(def, id);
						machineContext.getReferences().put(id, def);
						defsList.add(def);

						valueOfIdentifier.put(id, val);
						removeIdentifier(ids, id);
						newRun = true;
						break;
					}
				}
			}
		}

		if (!defsList.isEmpty()) {
			ADefinitionsMachineClause clause = machineContext.getDefinitionMachineClause();
			if (null == clause) {
				clause = new ADefinitionsMachineClause(defsList);
				machineContext.getAbstractMachineParseUnit().getMachineClauses().add(clause);
				machineContext.setDefinitionsMachineClause(clause);
			} else {
				clause.getDefinitions().addAll(defsList);
			}
		}

	}

	private void removeConstant(AIdentifierExpression id) {
		HashMap<String, Node> constants = machineContext.getConstants();
		for (Map.Entry<String, Node> entry : constants.entrySet()) {
			if (entry.getValue() == id) {
				constants.remove(entry.getKey());
				break;
			}
		}
	}

	private void removeAssignmentInPropertiesClause(Node val) {
		AEqualPredicate equal = (AEqualPredicate) val.parent();
		Node parent = equal.parent();
		if (parent instanceof AConjunctPredicate) {
			AConjunctPredicate conjunction = (AConjunctPredicate) parent;
			PPredicate other;
			if (conjunction.getLeft() == equal) {
				other = conjunction.getRight();
			} else {
				other = conjunction.getLeft();
			}
			Node parentParent = conjunction.parent();
			if (parentParent instanceof APropertiesMachineClause) {
				((APropertiesMachineClause) parentParent).setPredicates(other);
			} else if (parentParent instanceof AConjunctPredicate) {
				if (((AConjunctPredicate) parentParent).getLeft() == parent) {
					((AConjunctPredicate) parentParent).setLeft(other);
				} else {
					((AConjunctPredicate) parentParent).setRight(other);
				}
			}
		} else if (parent instanceof APropertiesMachineClause) {
			machineContext.setPropertiesMachineClaus(null);
			machineContext.getAbstractMachineParseUnit().getMachineClauses().remove(parent);
		}
	}

	private void removeIdentifier(Collection<Node> collection, Node identifierToRemove) {
		for (Node id : collection) {
			HashSet<Node> idValues = valuesOfConstantsFinder.valuesOfIdentifierTable.get(id);
			for (Node val : idValues) {
				HashSet<Node> idsInVal = dependsOnIdentifierTable.get(val);
				idsInVal.remove(identifierToRemove);
			}
		}
	}

	class ConstantsInTreeFinder extends DepthFirstAdapter {
		@Override
		public void defaultIn(Node node) {
			dependsOnIdentifierTable.put(node, new HashSet<>());
		}

		@Override
		public void defaultOut(Node node) {
			HashSet<Node> set = dependsOnIdentifierTable.get(node);
			HashSet<Node> parentSet = dependsOnIdentifierTable.get(node.parent());
			parentSet.addAll(set);
		}

		@Override
		public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
			defaultIn(node);
			node.getPredicates().apply(this);
		}

		@Override
		public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
			defaultIn(node);
			node.getPredicates().apply(this);
		}

		@Override
		public void caseAIdentifierExpression(AIdentifierExpression node) {
			defaultIn(node);
			Node refNode = machineContext.getReferences().get(node);
			if (machineContext.getConstants().containsValue(refNode)) {
				HashSet<Node> set = dependsOnIdentifierTable.get(node);
				set.add(refNode);
			}
			// it must be a bounded variable
			defaultOut(node);
		}
	}

	class ValuesOfIdentifierFinder extends DepthFirstAdapter {
		private final Hashtable<Node, HashSet<Node>> valuesOfIdentifierTable;
		private final HashSet<Node> identifiers;

		public ValuesOfIdentifierFinder() {
			valuesOfIdentifierTable = new Hashtable<>();

			this.identifiers = new HashSet<>();
			identifiers.addAll(machineContext.getConstants().values());
			identifiers.addAll(machineContext.getScalarParameter().values());

			for (Node id : identifiers) {
				valuesOfIdentifierTable.put(id, new HashSet<>());
			}

			AConstraintsMachineClause constraints = machineContext.getConstraintMachineClause();
			if (constraints != null) {
				analysePredicate(constraints.getPredicates());
			}
			APropertiesMachineClause properties = machineContext.getPropertiesMachineClause();
			if (properties != null) {
				analysePredicate(properties.getPredicates());
			}
		}

		private void analysePredicate(Node n) {
			if (n instanceof AEqualPredicate) {
				analyseEqualsPredicate((AEqualPredicate) n);
			} else if (n instanceof AGreaterPredicate) {
				// analyseGreaterPredicate((AGreaterPredicate) n);
			} else if (n instanceof ALessEqualPredicate) {
				// analyseLessEqualPredicate((ALessEqualPredicate) n);
			} else if (n instanceof AConjunctPredicate) {
				analysePredicate(((AConjunctPredicate) n).getLeft());
				analysePredicate(((AConjunctPredicate) n).getRight());
			}

		}

		private void analyseEqualsPredicate(AEqualPredicate node) {
			PExpression left = node.getLeft();
			Node left_ref = machineContext.getReferences().get(left);
			PExpression right = node.getRight();
			Node right_ref = machineContext.getReferences().get(right);

			if (left instanceof ACardExpression) {
				Node ref = machineContext.getReferences().get(((ACardExpression) left).getExpression());
				try {
					AIntegerExpression intExpr = (AIntegerExpression) right;
					int size = Integer.parseInt(intExpr.getLiteral().getText());
					integerValueTable.put(ref, size);
				} catch (ClassCastException e) {
				}
			}

			if (right instanceof ACardExpression) {
				Node ref = machineContext.getReferences().get(
						((ACardExpression) right).getExpression());
				try {
					AIntegerExpression intExpr = (AIntegerExpression) left;
					int size = Integer.parseInt(intExpr.getLiteral().getText());
					integerValueTable.put(ref, size);
				} catch (ClassCastException ignored) {
				}
			}

			if (identifiers.contains(left_ref)) {
				valuesOfIdentifierTable.get(left_ref).add(right);
			}

			if (identifiers.contains(right_ref)) {
				valuesOfIdentifierTable.get(right_ref).add(left);
			}
		}

	}

}
