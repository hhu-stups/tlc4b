package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesElementOfSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APrimedIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.util.Utils;
import de.tlc4b.exceptions.ScopeException;

public class PrimedNodesMarker extends DepthFirstAdapter {
	private ArrayList<POperation> operations;
	private MachineContext machineContext;
	private HashSet<Node> primedNodes;

	private HashSet<Node> nodesToPrime;

	public PrimedNodesMarker(ArrayList<POperation> operations,
			MachineContext machineContext) {
		this.primedNodes = new HashSet<Node>();
		this.operations = operations;
		this.machineContext = machineContext;
	}

	public void start() {
		for (Node def : machineContext.getDefinitions().values()) {
			def.apply(this);
		}
		for (POperation pOperation : operations) {
			pOperation.apply(this);
		}
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		for (PExpression e : copy) {
			Node ref = machineContext.getReferences().get(e);
			if (machineContext.getVariables().values().contains(ref)) {
				primedNodes.add(e);
			}

		}
	}

	@Override
	public void caseABecomesElementOfSubstitution(
			ABecomesElementOfSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			Node ref = machineContext.getReferences().get(e);
			if (machineContext.getVariables().values().contains(ref)) {
				primedNodes.add(e);
			}
		}
	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		nodesToPrime = new HashSet<Node>();
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			Node ref = machineContext.getReferences().get(e);
			nodesToPrime.add(ref);
			primedNodes.add(e);
		}
		node.getPredicate().apply(this);
		nodesToPrime = null;
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (nodesToPrime != null) {
			Node ref = machineContext.getReferences().get(node);
			if (nodesToPrime.contains(ref)) {
				primedNodes.add(node);
			}
		}
	}

	@Override
	public void caseAPrimedIdentifierExpression(APrimedIdentifierExpression node) {
		if(nodesToPrime != null){
			Node ref = machineContext.getReferences().get(node);
			if (nodesToPrime.contains(ref)) {
				return;
			}
		}
		String name = Utils.getTIdentifierListAsString(node.getIdentifier());
		throw new ScopeException("Unkown identifier: '"+name+"$0'");
	}

	public boolean isPrimed(Node node) {
		return primedNodes.contains(node);
	}
}
