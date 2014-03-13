package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.APredicateParseUnit;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;

/**
 * In this class the order of constants is determined. Constants can depend on
 * other constants: as an example in the expression k = k2 + 1 the value of the
 * constant k depends on k2. Constants are translated as definitions to TLA+ and
 * these definitions must be in order.
 * 
 */
public class ConstantsEvaluator extends DepthFirstAdapter {
	private Hashtable<Node, HashSet<Node>> dependsOnIdentifierTable;
	private MachineContext machineContext;
	private ValuesOfIdentifierFinder valuesOfConstantsFinder;
	private HashMap<Node, Integer> integerValueTable;
	private final ArrayList<Node> propertiesList;
	private final ArrayList<Node> invariantList;

	private LinkedHashMap<Node, Node> valueOfIdentifier;

	public Node getValueOfConstant(Node con) {
		return valueOfIdentifier.get(con);
	}

	public ArrayList<Node> getInvariantList() {
		return this.invariantList;
	}

	public ArrayList<Node> getPropertiesList() {
		return this.propertiesList;
	}

	public LinkedHashMap<Node, Node> getValueOfIdentifierMap() {
		return valueOfIdentifier;
	}
	
	public Integer getIntValue(Node node) {
		return integerValueTable.get(node);
	}

	public ArrayList<PExpression> getRangeOfIdentifier(Node con){;
		return valuesOfConstantsFinder.rangeOfIdentifierTable.get(con);
	}
	
	public ConstantsEvaluator(MachineContext machineContext) {
		this.dependsOnIdentifierTable = new Hashtable<Node, HashSet<Node>>();
		this.integerValueTable = new HashMap<Node, Integer>();
		this.machineContext = machineContext;
		this.propertiesList = new ArrayList<Node>();
		this.invariantList = new ArrayList<Node>();

		ConstantsInTreeFinder constantInTreeFinder = new ConstantsInTreeFinder();

		if (machineContext.getConstantsSetup() != null) {
			machineContext.getConstantsSetup().apply(constantInTreeFinder);
		}

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

		this.valueOfIdentifier = new LinkedHashMap<Node, Node>();

		evalIdentifier(machineContext.getConstants().values());

		evalIdentifier(machineContext.getScalarParameter().values());
	}

	private void evalIdentifier(Collection<Node> ids) {
		boolean newRun = true;
		while (newRun) {
			newRun = false;
			Iterator<Node> itr = ids.iterator();
			while (itr.hasNext()) {
				Node id = itr.next();
				if (valueOfIdentifier.containsKey(id))
					continue;
				HashSet<Node> idValues = valuesOfConstantsFinder.valuesOfIdentifierTable
						.get(id);
				for (Node val : idValues) {
					HashSet<Node> idsInVal = dependsOnIdentifierTable.get(val);
					if (idsInVal.size() == 0) {
						valueOfIdentifier.put(id, val);
						removeIdentifier(ids, id);
						newRun = true;
						break;
					}
				}
			}
		}
	}

	private void removeIdentifier(Collection<Node> collection,
			Node identifierToRemove) {
		Iterator<Node> itr = collection.iterator();
		while (itr.hasNext()) {
			Node id = itr.next();
			HashSet<Node> idValues = valuesOfConstantsFinder.valuesOfIdentifierTable
					.get(id);
			for (Node val : idValues) {
				HashSet<Node> idsInVal = dependsOnIdentifierTable.get(val);
				idsInVal.remove(identifierToRemove);
			}
		}
	}

	class ConstantsInTreeFinder extends DepthFirstAdapter {
		@Override
		public void defaultIn(Node node) {
			dependsOnIdentifierTable.put(node, new HashSet<Node>());
		}

		@Override
		public void defaultOut(Node node) {
			HashSet<Node> set = dependsOnIdentifierTable.get(node);
			Node parent = node.parent();
			HashSet<Node> parentSet = dependsOnIdentifierTable.get(parent);
			if (parentSet != null) {
				parentSet.addAll(set);
			}

		}

		@Override
		public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
			defaultIn(node);
			node.getPredicates().apply(this);
		}

		@Override
		public void caseAPredicateParseUnit(APredicateParseUnit node) {
			defaultIn(node);
			node.getPredicate();
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
		private Hashtable<Node, HashSet<Node>> valuesOfIdentifierTable;
		private Hashtable<Node, ArrayList<PExpression>> rangeOfIdentifierTable;
		private HashSet<Node> identifiers;

		public ValuesOfIdentifierFinder() {
			this.valuesOfIdentifierTable = new Hashtable<Node, HashSet<Node>>();
			this.rangeOfIdentifierTable = new Hashtable<Node, ArrayList<PExpression>>();

			this.identifiers = new HashSet<Node>();
			this.identifiers.addAll(machineContext.getConstants().values());
			this.identifiers.addAll(machineContext.getScalarParameter()
					.values());

			Iterator<Node> itr = identifiers.iterator();
			while (itr.hasNext()) {
				Node id = itr.next();
				valuesOfIdentifierTable.put(id, new HashSet<Node>());
				rangeOfIdentifierTable.put(id, new ArrayList<PExpression>());
			}

			Node constraints = machineContext.getConstraintMachineClause();
			if (constraints != null) {
				analysePredicate(
						((AConstraintsMachineClause) constraints)
								.getPredicates(),
						false);
			}

			if (machineContext.getConstantsSetup() != null) {
				if (machineContext.getConstantsSetup() instanceof ADisjunctPredicate) {
					analyseConstantSetupPredicate(machineContext
							.getConstantsSetup());
					
					for (Node con : this.identifiers) {
						ArrayList<PExpression> list = rangeOfIdentifierTable.get(con);
						if(list.size() == 1){
							// there only one value for the constant con, hence con remains a constant 
							valuesOfIdentifierTable.get(con).add(list.get(0));
						}
					}
				}else{
					analysePredicate(machineContext.getConstantsSetup(), true);
				}
				

			}

			Node properties = machineContext.getPropertiesMachineClause();
			if (properties != null) {
				PPredicate predicate = (PPredicate) ((APropertiesMachineClause) properties)
						.getPredicates();
				analysePredicate(predicate, true);

			}

			Node invariantClause = machineContext.getInvariantMachineClause();
			if (invariantClause != null) {
				analyseInvariantPredicate(((AInvariantMachineClause) invariantClause)
						.getPredicates());
			}
		}

		private void analyseConstantSetupPredicate(PPredicate constantsSetup) {
			if (constantsSetup instanceof ADisjunctPredicate) {
				ADisjunctPredicate dis = (ADisjunctPredicate) constantsSetup;
				analyseConstantSetupPredicate(dis.getLeft());
				analyseConstantSetupPredicate(dis.getRight());
			} else if (constantsSetup instanceof AConjunctPredicate) {
				AConjunctPredicate con = (AConjunctPredicate) constantsSetup;
				analyseConstantSetupPredicate(con.getLeft());
				analyseConstantSetupPredicate(con.getRight());
			} else if (constantsSetup instanceof AEqualPredicate) {
				AEqualPredicate equals = (AEqualPredicate) constantsSetup;
				PExpression left = equals.getLeft();
				Node left_ref = machineContext.getReferences().get(left);
				ArrayList<PExpression> currentRange = rangeOfIdentifierTable.get(left_ref);
				
				boolean found = false;
				for (PExpression pExpression : currentRange) {
					if(pExpression.toString().equals(equals.getRight().toString())){
						found = true;
					}
				}
				if(found == false){
					currentRange.add((PExpression) equals.getRight());
				}
				
			}

		}

		private void analyseInvariantPredicate(Node node) {
			if (node instanceof AConjunctPredicate) {
				AConjunctPredicate conjunction = (AConjunctPredicate) node;
				analyseInvariantPredicate(conjunction.getLeft());
				analyseInvariantPredicate(conjunction.getRight());
				return;
			}

			invariantList.add(node);
		}

		private void analysePredicate(Node node, boolean isProperties) {
			if (node instanceof AEqualPredicate) {
				analyseEqualsPredicate((AEqualPredicate) node);
			} else if (node instanceof AConjunctPredicate) {
				AConjunctPredicate conjunction = (AConjunctPredicate) node;
				analysePredicate(conjunction.getLeft(), isProperties);
				analysePredicate(conjunction.getRight(), isProperties);
				return;
			}

			if (isProperties) {
				propertiesList.add((PPredicate) node);
			}
		}

		private void analyseEqualsPredicate(AEqualPredicate node) {
			PExpression left = node.getLeft();
			Node left_ref = machineContext.getReferences().get(left);
			PExpression right = node.getRight();
			Node right_ref = machineContext.getReferences().get(right);

			if (left instanceof ACardExpression) {
				Node ref = machineContext.getReferences().get(
						((ACardExpression) left).getExpression());
				if (!machineContext.getConstants().containsValue(ref)) {
					try {
						AIntegerExpression intExpr = (AIntegerExpression) right;
						int size = Integer.parseInt(intExpr.getLiteral()
								.getText());
						integerValueTable.put(ref, size);
					} catch (ClassCastException e) {
					}
				}
			}

			if (right instanceof ACardExpression) {
				Node ref = machineContext.getReferences().get(
						((ACardExpression) right).getExpression());
				if (!machineContext.getConstants().containsValue(ref)) {
					try {
						AIntegerExpression intExpr = (AIntegerExpression) left;
						int size = Integer.parseInt(intExpr.getLiteral()
								.getText());
						integerValueTable.put(ref, size);
					} catch (ClassCastException e) {
					}
				}
			}

			if (identifiers.contains(left_ref)) {
				valuesOfIdentifierTable.get(left_ref).add(right);
			}

			if (identifiers.contains(right_ref)) {
				valuesOfIdentifierTable.get(right_ref).add(left);
			}
			return;

		}

	}

}
