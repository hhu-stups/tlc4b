package b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import b2tla.analysis.nodes.ElementOfNode;
import b2tla.analysis.nodes.EqualsNode;
import b2tla.analysis.nodes.NodeType;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.Start;

public class TypeRestrictor extends DepthFirstAdapter {

	private MachineContext machineContext;
	private ConstantExpressionFinder cEF;

	private Hashtable<Node, NodeType> restrictedTypes;

	public TypeRestrictor(Start start, MachineContext machineContext,
			Typechecker typechecker) {
		this.machineContext = machineContext;
		restrictedTypes = new Hashtable<Node, NodeType>();

		cEF = new ConstantExpressionFinder(start, machineContext);
	}

	public Hashtable<Node, NodeType> getRestrictedTypes() {
		return restrictedTypes;
	}

	private void putRestrictedType(Node identifier, NodeType expression) {
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
		inAPropertiesMachineClause(node);
		HashSet<Node> list = new HashSet<Node>(machineContext.getConstants()
				.values());
		analysePredicate(node.getPredicates(), list);

		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		outAPropertiesMachineClause(node);
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
			} else if (list.contains(r_right) && cEF.isconstant(left)) {
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
			} else if (list.contains(r_right) && cEF.isconstant(left)) {
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

}
