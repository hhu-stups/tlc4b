package de.tlc4b.analysis.typerestriction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AIntersectionExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALetSubstitution;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.ANotMemberPredicate;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.APreconditionSubstitution;
import de.be4.classicalb.core.parser.node.APredicateParseUnit;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetSubtractionExpression;
import de.be4.classicalb.core.parser.node.ASubsetPredicate;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.ltl.core.parser.node.AExistsLtl;
import de.be4.ltl.core.parser.node.AForallLtl;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.ConstantsEvaluator;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.btypes.BType;
import de.tlc4b.exceptions.NotSupportedException;
import de.tlc4b.ltl.LTLFormulaVisitor;
import de.tlc4b.util.UtilMethods;

public class TypeRestrictor extends DepthFirstAdapter {

	private final MachineContext machineContext;
	private final IdentifierDependencies identifierDependencies;
	private final Typechecker typechecker;
	private final ConstantsEvaluator constantsEvaluator;

	private final Hashtable<Node, Node> restrictedTypeNodeTable;
	private final HashSet<Node> removedNodes;

	private final Hashtable<Node, ArrayList<Node>> restrictedNodeTable;
	private final Hashtable<Node, ArrayList<Node>> subtractedNodeTable;

	public Node getRestrictedNode(Node node) {
		return restrictedTypeNodeTable.get(node);
	}

	public Collection<Node> getAllRestrictedNodes() {
		return restrictedTypeNodeTable.values();
	}

	public TypeRestrictor(Start start, MachineContext machineContext,
			Typechecker typechecker, ConstantsEvaluator constantsEvaluator) {
		this.machineContext = machineContext;
		this.typechecker = typechecker;
		this.constantsEvaluator = constantsEvaluator;

		this.restrictedTypeNodeTable = new Hashtable<Node, Node>();
		this.removedNodes = new HashSet<Node>();

		this.restrictedNodeTable = new Hashtable<Node, ArrayList<Node>>();
		this.subtractedNodeTable = new Hashtable<Node, ArrayList<Node>>();

		this.identifierDependencies = new IdentifierDependencies(machineContext);

		start.apply(this);

		checkLTLFormulas();
	}

	private void checkLTLFormulas() {
		for (LTLFormulaVisitor visitor : machineContext.getLTLFormulas()) {

			for (de.be4.ltl.core.parser.node.Node ltlNode : visitor
					.getUnparsedHashTable().keySet()) {
				Node bNode = visitor.getBAst(ltlNode);

				if (ltlNode instanceof AExistsLtl) {
					Node id = visitor.getLTLIdentifier(((AExistsLtl) ltlNode)
							.getExistsIdentifier().getText());
					HashSet<Node> list = new HashSet<Node>();
					list.add(id);
					analysePredicate(bNode, list, new HashSet<Node>());

					PExpression e = (PExpression) id;
					HashSet<PExpression> set = new HashSet<PExpression>();
					set.add(e);
					createRestrictedTypeofLocalVariables(set, true);
				} else if (ltlNode instanceof AForallLtl) {
					Node id = visitor.getLTLIdentifier(((AForallLtl) ltlNode)
							.getForallIdentifier().getText());
					HashSet<Node> list = new HashSet<Node>();
					list.add(id);
					analysePredicate(bNode, list, new HashSet<Node>());

					PExpression e = (PExpression) id;
					HashSet<PExpression> set = new HashSet<PExpression>();
					set.add(e);
					createRestrictedTypeofLocalVariables(set, true);
				}
				bNode.apply(this);
			}

		}
	}

	public boolean isARemovedNode(Node node) {
		return this.removedNodes.contains(node);
	}

	private void putRestrictedType(Node identifier, Node expression) {
		ArrayList<Node> list = restrictedNodeTable.get(identifier);

		if (list == null) {
			list = new ArrayList<Node>();
			list.add(expression);
			restrictedNodeTable.put(identifier, list);
		} else {
			if (!list.contains(expression)) {
				list.add(expression);
			}
		}
	}

	private void putSubstractedType(Node identifier, Node expression) {
		ArrayList<Node> list = subtractedNodeTable.get(identifier);
		if (list == null) {
			list = new ArrayList<Node>();
			list.add(expression);
			subtractedNodeTable.put(identifier, list);
		} else {
			list.add(expression);
		}
	}

	@Override
	public void inAConstraintsMachineClause(AConstraintsMachineClause node) {
		HashSet<Node> list = new HashSet<Node>();
		// list.addAll(machineContext.getSetParamter().values());
		list.addAll(machineContext.getScalarParameter().values());
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		HashSet<PExpression> set = new HashSet<PExpression>();
		for (Node param : list) {
			set.add((PExpression) param);
		}
		createRestrictedTypeofLocalVariables(new HashSet<PExpression>(set),
				false);
	}

	@Override
	public void inAPropertiesMachineClause(APropertiesMachineClause node) {
		HashSet<PExpression> set = new HashSet<PExpression>();
		for (Node con : machineContext.getConstants().values()) {
			set.add((PExpression) con);
			Node valueOfConstant = constantsEvaluator.getValueOfConstant(con);
			if(valueOfConstant!= null){
				removedNodes.add(valueOfConstant.parent());
			}
			
		}
		HashSet<Node> list = new HashSet<Node>();
		list.addAll(machineContext.getConstants().values());
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		

		createRestrictedTypeofLocalVariables(new HashSet<PExpression>(set),
				false);
	}

	public void analyseDisjunktionPredicate(PPredicate node, HashSet<Node> list) {
		if (node instanceof ADisjunctPredicate) {
			ADisjunctPredicate dis = (ADisjunctPredicate) node;
			analyseDisjunktionPredicate(dis.getLeft(), list);
			analyseDisjunktionPredicate(dis.getRight(), list);
		} else {
			analysePredicate(node, list, new HashSet<Node>());
		}
	}

	private void analysePredicate(Node n, HashSet<Node> list,
			HashSet<Node> ignoreList) {

		if (removedNodes.contains(n))
			return;

		if (n instanceof AEqualPredicate) {
			PExpression left = ((AEqualPredicate) n).getLeft();
			Node r_left = machineContext.getReferenceNode(left);
			PExpression right = ((AEqualPredicate) n).getRight();
			Node r_right = machineContext.getReferenceNode(right);

			if (list.contains(r_left)
					&& isAConstantExpression(right, list, ignoreList)) {
				right.apply(this);
				ArrayList<PExpression> element = new ArrayList<PExpression>();
				element.add(right);
				if (machineContext.getVariables().values().contains(r_left)) {
					r_left = variablesHashTable.get(r_left);
				}
				putRestrictedType(r_left, new ASetExtensionExpression(element));
				removedNodes.add(n);
			}
			if (list.contains(r_right)
					&& isAConstantExpression(left, list, ignoreList)) {
				left.apply(this);
				ArrayList<PExpression> element = new ArrayList<PExpression>();
				element.add(left);
				if (machineContext.getVariables().values().contains(r_right)) {
					r_right = variablesHashTable.get(r_right);
				}
				putRestrictedType(r_right, new ASetExtensionExpression(element));
				removedNodes.add(n);
			}
			// detecting couples, e.g. (a,b) = (1,3)
			// if (left instanceof ACoupleExpression) {
			// ACoupleExpression couple = (ACoupleExpression) left;
			// PExpression first = couple.getList().get(0);
			// Node r_first = machineContext.getReferenceNode(first);
			// PExpression second = couple.getList().get(0);
			// Node r_second = machineContext.getReferenceNode(second);
			//
			// if (list.contains(r_first) && list.contains(r_second)
			// && isAConstantExpression(right, list, ignoreList)) {
			// ArrayList<PExpression> element = new ArrayList<PExpression>();
			// element.add(right);
			// putRestrictedTypeOfTuple(r_right,
			// new ASetExtensionExpression(element));
			// removedNodes.add(n);
			// }
			// }

			return;
		}

		if (n instanceof AMemberPredicate) {
			PExpression left = ((AMemberPredicate) n).getLeft();
			Node r_left = machineContext.getReferenceNode(left);
			PExpression right = ((AMemberPredicate) n).getRight();
			if (list.contains(r_left)
					&& isAConstantExpression(right, list, ignoreList)) {
				if (machineContext.getVariables().values().contains(r_left)) {
					r_left = variablesHashTable.get(r_left);
				}
				putRestrictedType(r_left, right);
				removedNodes.add(n);
			}
			return;
		}

		if (n instanceof ANotMemberPredicate) {
			PExpression left = ((ANotMemberPredicate) n).getLeft();
			Node r_left = machineContext.getReferenceNode(left);
			PExpression right = ((ANotMemberPredicate) n).getRight();
			if (list.contains(r_left)
					&& isAConstantExpression(right, list, ignoreList)) {
				if (machineContext.getVariables().values().contains(r_left)) {
					r_left = variablesHashTable.get(r_left);
				}
				putSubstractedType(r_left, right);
				removedNodes.add(n);
			}
			return;
		}

		if (n instanceof ASubsetPredicate) {
			PExpression left = ((ASubsetPredicate) n).getLeft();
			Node r_left = machineContext.getReferenceNode(left);
			PExpression right = ((ASubsetPredicate) n).getRight();

			if (list.contains(r_left)
					&& isAConstantExpression(right, list, ignoreList)) {
				right.apply(this);
				if (machineContext.getVariables().values().contains(r_left)) {
					r_left = variablesHashTable.get(r_left);
				}
				putRestrictedType(r_left, new APowSubsetExpression(right));
				removedNodes.add(n);
			}
			return;
		}

		if (n instanceof AConjunctPredicate) {
			Node left = ((AConjunctPredicate) n).getLeft();
			Node right = ((AConjunctPredicate) n).getRight();
			analysePredicate(left, list, ignoreList);
			analysePredicate(right, list, ignoreList);
			if (removedNodes.contains(left) && removedNodes.contains(right)) {
				removedNodes.add(n);
			}
			return;
		}

		if (n instanceof AExistsPredicate) {
			HashSet<Node> set = new HashSet<Node>();
			for (PExpression e : ((AExistsPredicate) n).getIdentifiers()) {
				set.add(e);
			}
			set.addAll(ignoreList);
			analysePredicate(((AExistsPredicate) n).getPredicate(), list, set);
		}

		if (n instanceof Start) {
			analysePredicate(((Start) n).getPParseUnit(), list, ignoreList);
		}

		if (n instanceof APredicateParseUnit) {
			analysePredicate(((APredicateParseUnit) n).getPredicate(), list,
					ignoreList);
			return;
		}
	}

	public boolean isAConstantExpression(Node node, HashSet<Node> list,
			HashSet<Node> ignoreList) {
		HashSet<Node> newList = new HashSet<Node>();
		newList.addAll(list);
		newList.addAll(ignoreList);
		if (identifierDependencies.containsIdentifier(node, newList)) {
			return false;
		}
		return true;
	}

	@Override
	public void inAForallPredicate(AForallPredicate node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		AImplicationPredicate implication = (AImplicationPredicate) node
				.getImplication();
		analysePredicate(implication.getLeft(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inAExistsPredicate(AExistsPredicate node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicate(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inAComprehensionSetExpression(AComprehensionSetExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inALambdaExpression(ALambdaExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicate(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	public void inAGeneralSumExpression(AGeneralSumExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	public void inAGeneralProductExpression(AGeneralProductExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	private Hashtable<Node, HashSet<PExpression>> expectedIdentifieListTable = new Hashtable<Node, HashSet<PExpression>>();

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		expectedIdentifieListTable.put(node.getSubstitutions(),
				new HashSet<PExpression>());
		node.getSubstitutions().apply(this);
	}

	@Override
	public void caseAOperation(AOperation node) {
		HashSet<PExpression> list = new HashSet<PExpression>();
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				list.add(e);
			}
		}
		expectedIdentifieListTable.put(node.getOperationBody(), list);
		if (node.getOperationBody() != null) {
			node.getOperationBody().apply(this);
		}
		createRestrictedTypeofLocalVariables(list, false);
	}

	@Override
	public void inAPreconditionSubstitution(APreconditionSubstitution node) {
		HashSet<Node> set = new HashSet<Node>(getExpectedIdentifier(node));
		analysePredicate(node.getPredicate(), set, new HashSet<Node>());
	}

	private HashSet<PExpression> getExpectedIdentifier(Node node) {
		HashSet<PExpression> list = expectedIdentifieListTable.get(node);
		if (list == null)
			list = new HashSet<PExpression>();
		return list;
	}

	@Override
	public void inASelectSubstitution(ASelectSubstitution node) {
		HashSet<Node> list = new HashSet<Node>(getExpectedIdentifier(node));
		analysePredicate(node.getCondition(), list, new HashSet<Node>());
	}

	@Override
	public void inAAnySubstitution(AAnySubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		list.addAll(getExpectedIdentifier(node));
		analysePredicate(node.getWhere(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	@Override
	public void inALetSubstitution(ALetSubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		list.addAll(getExpectedIdentifier(node));
		analysePredicate(node.getPredicate(), list, new HashSet<Node>());
		createRestrictedTypeofLocalVariables(
				new HashSet<PExpression>(node.getIdentifiers()), false);
	}

	private Hashtable<Node, Node> variablesHashTable;

	public void inABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		if (!(node.getPredicate() instanceof AExistsPredicate)) {
			variablesHashTable = new Hashtable<Node, Node>();

			HashSet<Node> list = new HashSet<Node>();
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				Node ref = machineContext.getReferenceNode(e);

				list.add(ref);
				variablesHashTable.put(ref, e);
			}
			analysePredicate(node.getPredicate(), list, new HashSet<Node>());
			createRestrictedTypeofLocalVariables(
					new HashSet<PExpression>(copy), false);
		}
	}

	private void createRestrictedTypeofLocalVariables(Set<PExpression> copy,
			boolean constant) {
		// TODO if constant is true, only constant expressions should be used to
		// restrict the type.
		// This is required by the TLC model checker when checking an LTL
		// formula.

		for (PExpression e : copy) {
			if (constantsEvaluator.getValueOfIdentifierMap().containsKey(e)) {
				continue;
			}

			PExpression tree = null;
			ArrayList<Node> restrictedList = restrictedNodeTable.get(e);
			if (restrictedList == null) {
				BType conType = typechecker.getType(e);
				if (conType == null) {
					conType = typechecker.getType(machineContext
							.getReferenceNode(e));
				}
				if (conType.containsInfiniteType()
						&& !(e.parent() instanceof ALambdaExpression)
						&& !(e.parent() instanceof AComprehensionSetExpression)) {
					AIdentifierExpression id = (AIdentifierExpression) e;
					String localVariableName = Utils.getIdentifierAsString(id
							.getIdentifier());
					throw new NotSupportedException(
							"Unable to restrict the type '"
									+ conType
									+ "' of identifier '"
									+ localVariableName
									+ "' to a finite set. TLC is not able to handle infinite sets.\n"
									+ UtilMethods.getPositionAsString(e));
				}

				tree = conType.createSyntaxTreeNode(typechecker);
			} else {
				tree = (PExpression) restrictedList.get(0);
				for (int i = 1; i < restrictedList.size(); i++) {
					PExpression n = (PExpression) restrictedList.get(i);
					tree = new AIntersectionExpression(tree, n);
				}

			}
			ArrayList<Node> substractedList = subtractedNodeTable.get(e);
			if (substractedList != null) {
				for (int i = 0; i < substractedList.size(); i++) {
					PExpression n = (PExpression) substractedList.get(i);
					tree = new ASetSubtractionExpression(tree, n);

				}
			}
			this.restrictedTypeNodeTable.put(e, tree);
		}
	}

	@Override
	public void caseAAssertionsMachineClause(AAssertionsMachineClause node) {
		if (TLC4BGlobals.isAssertion()) {
			List<PPredicate> copy = new ArrayList<PPredicate>(
					node.getPredicates());
			for (PPredicate e : copy) {
				e.apply(this);
			}
		}
	}

	public void addRemoveNode(Node node) {
		this.removedNodes.add(node);
	}

}
