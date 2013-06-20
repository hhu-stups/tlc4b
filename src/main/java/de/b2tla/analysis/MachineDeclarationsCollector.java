package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;

import de.b2tla.exceptions.ScopeException;
import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.ASeesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class MachineDeclarationsCollector extends DepthFirstAdapter {

	private String machineName;
	private final Node start;

	private final Hashtable<String, Node> machineParameters;
	private final Hashtable<String, Node> deferredSets;
	private final Hashtable<String, Node> enumeratedSets;
	private final Hashtable<String, Node> enumValues;
	private final Hashtable<String, Node> constants;
	private final Hashtable<String, Node> variables;
	private final Hashtable<String, Node> operations;

	private final Hashtable<String, AIdentifierExpression> seenMachines;

	public MachineDeclarationsCollector(Node start) {
		this.start = start;
		machineParameters = new Hashtable<String, Node>();
		deferredSets = new Hashtable<String, Node>();
		enumeratedSets = new Hashtable<String, Node>();
		enumValues = new Hashtable<String, Node>();
		constants = new Hashtable<String, Node>();
		variables = new Hashtable<String, Node>();
		operations = new Hashtable<String, Node>();
		seenMachines = new Hashtable<String, AIdentifierExpression>();

		start.apply(this);
	}

	public String getName() {
		return machineName;
	}

	public Node getStart() {
		return start;
	}

	public Hashtable<String, Node> getConstants() {
		return constants;
	}

	public Hashtable<String, Node> getVariables() {
		return variables;
	}

	public Hashtable<String, Node> getOperations() {
		return operations;
	}

	public Hashtable<String, Node> getDeferredSets() {
		return deferredSets;
	}

	public Hashtable<String, Node> getEnumeratedSets() {
		return enumeratedSets;
	}

	public Hashtable<String, Node> getEnumValues() {
		return enumValues;
	}

	public Hashtable<String, Node> getMachineParameters() {
		return machineParameters;
	}

	public Hashtable<String, AIdentifierExpression> getSeenMachines() {
		return seenMachines;
	}

	private void exist(LinkedList<TIdentifierLiteral> list) {
		String name = Utils.getIdentifierAsString(list);
		if (constants.containsKey(name) || variables.containsKey(name)
				|| operations.containsKey(name)
				|| deferredSets.containsKey(name)
				|| enumeratedSets.containsKey(name)
				|| enumValues.containsKey(name)
				|| machineParameters.containsKey(name)
				|| seenMachines.containsKey(name)) {
			throw new ScopeException("Duplicate identifier: '" + name + "'");
		}
	}

	@Override
	public void caseASeesMachineClause(ASeesMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getMachineNames());
		for (PExpression e : copy) {
			AIdentifierExpression p = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(p.getIdentifier());

			try {
				exist(p.getIdentifier());
			} catch (ScopeException e2) {
				throw new ScopeException("Machine '" + name
						+ "' is seen twice.");
			}

			seenMachines.put(name, p);
		}
	}

	@Override
	public void caseAMachineHeader(AMachineHeader node) {
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getName());
			machineName = Utils.getIdentifierAsString(copy);

		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				AIdentifierExpression p = (AIdentifierExpression) e;
				String name = Utils.getIdentifierAsString(p.getIdentifier());
				exist(p.getIdentifier());
				machineParameters.put(name, p);
			}
		}
	}
	
	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression c = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(c.getIdentifier());
			exist(c.getIdentifier());
			constants.put(name, c);
		}
	}

	@Override
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(v.getIdentifier());
			exist(v.getIdentifier());
			variables.put(name, v);
		}
	}

	@Override
	public void caseADeferredSetSet(ADeferredSetSet node) {
		List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
				node.getIdentifier());
		String name = Utils.getIdentifierAsString(copy);
		exist(node.getIdentifier());
		deferredSets.put(name, node);
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());
			String name = Utils.getIdentifierAsString(copy);
			exist(node.getIdentifier());
			enumeratedSets.put(name, node);
		}
		List<PExpression> copy = new ArrayList<PExpression>(node.getElements());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(v.getIdentifier());
			exist(v.getIdentifier());
			enumValues.put(name, v);
		}
	}

	@Override
	public void caseAOperation(AOperation node) {
		String name = Utils.getIdentifierAsString(node.getOpName());
		exist(node.getOpName());
		operations.put(name, node);
	}

}
