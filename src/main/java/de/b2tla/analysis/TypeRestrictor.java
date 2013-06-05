package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.b2tla.analysis.nodes.ElementOfNode;
import de.b2tla.analysis.nodes.EqualsNode;
import de.b2tla.analysis.nodes.NodeType;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALetSubstitution;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.APreconditionSubstitution;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASubsetPredicate;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.Start;

public class TypeRestrictor extends DepthFirstAdapter {

	private MachineContext machineContext;
	private ConstantExpressionFinder cEF;

	private Hashtable<Node, NodeType> restrictedTypes;
	private Hashtable<Node, ArrayList<NodeType>> restrictedTypesSet;

	public TypeRestrictor(Start start, MachineContext machineContext,
			Typechecker typechecker) {
		this.machineContext = machineContext;
		restrictedTypes = new Hashtable<Node, NodeType>();
		restrictedTypesSet = new Hashtable<Node, ArrayList<NodeType>>();

		cEF = new ConstantExpressionFinder(start, machineContext);
	}

	public Hashtable<Node, NodeType> getRestrictedTypes() {
		return restrictedTypes;
	}

	public ArrayList<NodeType> getRestrictedTypesSet(Node node) {
		return restrictedTypesSet.get(node);
	}

	private void putRestrictedType(Node identifier, NodeType expression) {
		ArrayList<NodeType> list = restrictedTypesSet.get(identifier);

		if (list == null) {
			list = new ArrayList<NodeType>();
			list.add(expression);
			restrictedTypesSet.put(identifier, list);
		} else {
			list.add(expression);
		}

		if (restrictedTypes.containsKey(identifier))
			return;

		restrictedTypes.put(identifier, expression);

	}

	@Override
	public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
		inAConstraintsMachineClause(node);
		HashSet<Node> list = new HashSet<Node>();
		list.addAll(machineContext.getSetParamter().values());
		list.addAll(machineContext.getScalarParameter().values());
		analysePredicate(node.getPredicates(), list);

		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		outAConstraintsMachineClause(node);
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		node.getPredicates().apply(this);
	}

	private void analysePredicate(Node n, HashSet<Node> list) {
		if (n instanceof AEqualPredicate) {
			PExpression left = ((AEqualPredicate) n).getLeft();
			Node r_left = machineContext.getReferences().get(left);
			PExpression right = ((AEqualPredicate) n).getRight();
			Node r_right = machineContext.getReferences().get(right);

			if (list.contains(r_left) && cEF.isconstant(right)) {
				EqualsNode setNode = new EqualsNode(right);
				putRestrictedType(r_left, setNode);
			}
			if (list.contains(r_right) && cEF.isconstant(left)) {
				EqualsNode setNode = new EqualsNode(left);
				putRestrictedType(r_right, setNode);
			}
			return;
		}

		if (n instanceof AMemberPredicate) {
			PExpression left = ((AMemberPredicate) n).getLeft();
			Node r_left = machineContext.getReferences().get(left);
			PExpression right = ((AMemberPredicate) n).getRight();
			Node r_right = machineContext.getReferences().get(right);

			if (list.contains(r_left) && cEF.isconstant(right)) {
				putRestrictedType(r_left, new ElementOfNode(right));
			}
			if (list.contains(r_right) && cEF.isconstant(left)) {
				putRestrictedType(r_right, new ElementOfNode(left));
			}
			return;

		}

		if (n instanceof AConjunctPredicate) {
			analysePredicate(((AConjunctPredicate) n).getLeft(), list);
			analysePredicate(((AConjunctPredicate) n).getRight(), list);
			return;
		}

	}

	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			// e.apply(this);
			list.add(e);
		}
		// TODO test if the expression is really a implication, currently a
		// class cast exception is thrown
		AImplicationPredicate implication = (AImplicationPredicate) node
				.getImplication();
		analysePredicate(implication.getLeft(), list);
		node.getImplication().apply(this);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			// e.apply(this);
			list.add(e);
		}
		analysePredicate(node.getPredicate(), list);
		node.getPredicate().apply(this);
	}

	@Override
	public void caseAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list);
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
	}

	@Override
	public void caseAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicates(), list);
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
			// e.apply(this);
		}
		analysePredicate(node.getPredicates(), list);
		node.getPredicates().apply(this);
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		analysePredicate(node.getPredicate(), list);
		node.getPredicate().apply(this);
		node.getExpression().apply(this);
	}

	private Hashtable<Node, HashSet<Node>> expectedIdentifieListTable = new Hashtable<Node, HashSet<Node>>();

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		expectedIdentifieListTable.put(node.getSubstitutions(),
				new HashSet<Node>());
		node.getSubstitutions().apply(this);
	}

	@Override
	public void caseAOperation(AOperation node) {
		HashSet<Node> list = new HashSet<Node>();
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getReturnValues());
			for (PExpression e : copy) {
				list.add(e);
			}
		}
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
	}

	@Override
	public void caseAPreconditionSubstitution(APreconditionSubstitution node) {
		HashSet<Node> list = getExpectedIdentifier(node);
		analysePredicate(node.getPredicate(), list);

		node.getPredicate().apply(this);
		node.getSubstitution().apply(this);
	}

	private HashSet<Node> getExpectedIdentifier(Node node) {
		HashSet<Node> list = expectedIdentifieListTable.get(node);
		if (list == null)
			list = new HashSet<Node>();
		return list;
	}

	@Override
	public void caseASelectSubstitution(ASelectSubstitution node) {
		HashSet<Node> list = getExpectedIdentifier(node);
		analysePredicate(node.getCondition(), list);
		node.getCondition().apply(this);
		node.getThen().apply(this);
		{
			List<PSubstitution> copy = new ArrayList<PSubstitution>(
					node.getWhenSubstitutions());
			for (PSubstitution e : copy) {
				e.apply(this);
			}
		}
		if (node.getElse() != null) {
			node.getElse().apply(this);
		}
	}

	@Override
	public void caseAAnySubstitution(AAnySubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		list.addAll(getExpectedIdentifier(node));
		analysePredicate(node.getWhere(), list);

		node.getWhere().apply(this);
		node.getThen().apply(this);
	}
	
    @Override
    public void caseALetSubstitution(ALetSubstitution node)
    {
    	HashSet<Node> list = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			list.add(e);
		}
		list.addAll(getExpectedIdentifier(node));
		analysePredicate(node.getPredicate(), list);

		node.getPredicate().apply(this);
		node.getSubstitution().apply(this);
    }
	
}
