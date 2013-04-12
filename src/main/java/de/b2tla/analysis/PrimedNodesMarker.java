package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesElementOfSubstitution;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.POperation;

public class PrimedNodesMarker extends DepthFirstAdapter {
	private ArrayList<POperation> operations;
	private MachineContext machineContext;

	private HashSet<Node> primedNodes;

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

	public boolean isPrimed(Node node) {
		return primedNodes.contains(node);
	}
}
