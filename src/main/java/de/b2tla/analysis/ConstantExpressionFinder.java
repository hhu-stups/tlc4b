package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.Start;

public class ConstantExpressionFinder extends DepthFirstAdapter {
	private MachineContext machineContext;

	private final int MAX_DEGREE = 20;

	private Hashtable<Node, Integer> constantDegree;

	// contains for each quantification a set of all bounded Variables
	private ArrayList<HashSet<Node>> contextTable;

	public boolean isconstant(Node node) {
		Integer degree = constantDegree.get(node);
		if (degree != null) {
			if (degree != 0)
				return true;
			else
				return false;
		}
		return true;
	}

	public ConstantExpressionFinder(Start start, MachineContext machineContext) {
		this.machineContext = machineContext;
		this.constantDegree = new Hashtable<Node, Integer>();

		this.contextTable = new ArrayList<HashSet<Node>>();
		contextTable.add(new HashSet<Node>(machineContext.getConstants()
				.values()));

		start.apply(this);

	}

	public void defaultOut(Node node) {
		Integer degree = constantDegree.get(node);
		setDegree(node.parent(), degree);

	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node refNode = machineContext.getReferences().get(node);
		if(machineContext.getConstants().values().contains(refNode)){
			constantDegree.put(node, 19);
			defaultOut(refNode); //TODO verify
			return;
		}
		int degree = 0;
		for (int i = contextTable.size() - 1; i >= 0; i--) {
			HashSet<Node> currentScope = contextTable.get(i);
			if (currentScope.contains(refNode)) {
				constantDegree.put(node, degree);
				defaultOut(node);
				return;
			}
			degree++;
		}
		constantDegree.put(node, MAX_DEGREE);
		constantDegree.put(node.parent(), MAX_DEGREE);

	}

	private void setDegree(Node node, Integer degree) {
		if (degree != null) {
			Integer oldDegree = constantDegree.get(node);
			if (oldDegree != null) {
				constantDegree.put(node, Math.max(degree, oldDegree));
			} else {
				constantDegree.put(node, degree);
			}
		}
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		if (node.getVariant() != null) {
			node.getVariant().apply(this);
		}

		if (node.getHeader() != null) {
			node.getHeader().apply(this);
		}
		{
			List<PMachineClause> copy = new ArrayList<PMachineClause>(
					node.getMachineClauses());

			for (PMachineClause e : copy) {
				e.apply(this);
			}
		}
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		node.getPredicates().apply(this);
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
	}

	@Override
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
	}

	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		HashSet<Node> set = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			set.add(e);
		}
		contextTable.add(set);
		node.getImplication().apply(this);
		contextTable.remove(contextTable.size() - 1);
		Integer degree = constantDegree.get(node);
		if (degree != null) {
			constantDegree.put(node, degree - 1);
		}
		outAForallPredicate(node);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		HashSet<Node> set = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			set.add(e);
		}
		contextTable.add(set);
		node.getPredicate().apply(this);
		contextTable.remove(contextTable.size() - 1);
		Integer degree = constantDegree.get(node);
		if (degree != null) {
			constantDegree.put(node, degree - 1);
		}
		outAExistsPredicate(node);
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		inALambdaExpression(node);
		HashSet<Node> set = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			set.add(e);
		}
		contextTable.add(set);
		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
		Integer degree = constantDegree.get(node);
		if (degree != null) {
			constantDegree.put(node, degree - 1);
		}
		outALambdaExpression(node);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		inAComprehensionSetExpression(node);
		HashSet<Node> set = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			set.add(e);
		}
		contextTable.add(set);
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
		Integer degree = constantDegree.get(node);
		if (degree != null) {
			constantDegree.put(node, degree - 1);
		}
		outAComprehensionSetExpression(node);
	}

}
