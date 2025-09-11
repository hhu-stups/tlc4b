package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesElementOfSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APrimedIdentifierExpression;
import de.be4.classicalb.core.parser.node.ARecordFieldExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.util.Utils;
import de.tlc4b.exceptions.NotSupportedException;
import de.tlc4b.exceptions.ScopeException;

public class PrimedNodesMarker extends DepthFirstAdapter {
	private final ArrayList<POperation> operations;
	private final MachineContext machineContext;
	private final HashSet<Node> primedNodes;

	private HashSet<Node> nodesToPrime;

	public PrimedNodesMarker(ArrayList<POperation> operations, MachineContext machineContext,
	                         Set<Node> primedNodes) {
		this.primedNodes = new HashSet<>(primedNodes);
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

	private void primeIfVariable(Node node) {
		Node ref = machineContext.getReferences().get(node);
		if (machineContext.getVariables().containsValue(ref)) {
			primedNodes.add(node);
		}
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getLhsExpression());
		for (PExpression e : copy) {
			primeWrittenVariable(e);
		}
	}

	private void primeWrittenVariable(PExpression e) {
		if (e instanceof AIdentifierExpression) {
			primeIfVariable(e);
		} else if (e instanceof AFunctionExpression) {
			primeWrittenVariable(((AFunctionExpression) e).getIdentifier());
		} else if (e instanceof ARecordFieldExpression) {
			primeWrittenVariable(((ARecordFieldExpression) e).getRecord());
		} else {
			throw new NotSupportedException("Unsupported assignment lhs: " + e);
		}
	}

	@Override
	public void caseABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
		for (PExpression e : copy) {
			Node ref = machineContext.getReferences().get(e);
			if (machineContext.getVariables().containsValue(ref)) {
				primedNodes.add(e);
			}
		}
	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		nodesToPrime = new HashSet<>();
		List<PExpression> copy = new ArrayList<>(node.getIdentifiers());
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
		if (nodesToPrime != null){
			Node ref = machineContext.getReferences().get(node);
			if (nodesToPrime.contains(ref)) {
				return;
			}
		}
		String name = Utils.getTIdentifierListAsString(node.getIdentifier());
		throw new ScopeException("Unknown identifier: '"+name+"$0'");
	}

	public boolean isPrimed(Node node) {
		return primedNodes.contains(node);
	}
}
