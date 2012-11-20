package analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AOpSubstitution;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ASeesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import exceptions.ScopeException;

public class MachineContext extends DepthFirstAdapter {

	private String machineName;
	private final Start start;
	private final Hashtable<String, MachineContext> machineContextsTable;

	private final Hashtable<String, Node> machineParameters;
	private final Hashtable<String, Node> deferredSets;
	private final Hashtable<String, Node> enumeratedSets;
	private final Hashtable<String, Node> enumValues;
	private final Hashtable<String, Node> constants;
	private final Hashtable<String, Node> variables;
	private final Hashtable<String, Node> operations;
	private final Hashtable<String, AIdentifierExpression> seenMachines;

	private ArrayList<Hashtable<String, Node>> contextTable;

	private final Hashtable<Node, Node> referencesTable;

	public MachineContext(Start start,
			Hashtable<String, MachineContext> machineContextsTable) {
		this.start = start;
		this.referencesTable = new Hashtable<Node, Node>();

		machineParameters = new Hashtable<String, Node>();
		deferredSets = new Hashtable<String, Node>();
		enumeratedSets = new Hashtable<String, Node>();
		enumValues = new Hashtable<String, Node>();
		constants = new Hashtable<String, Node>();
		variables = new Hashtable<String, Node>();
		operations = new Hashtable<String, Node>();
		seenMachines = new Hashtable<String, AIdentifierExpression>();

		this.machineContextsTable = machineContextsTable;

		start.apply(this);
	}

	public MachineContext(Start start) {
		this.start = start;
		this.referencesTable = new Hashtable<Node, Node>();

		machineParameters = new Hashtable<String, Node>();
		deferredSets = new Hashtable<String, Node>();
		enumeratedSets = new Hashtable<String, Node>();
		enumValues = new Hashtable<String, Node>();
		constants = new Hashtable<String, Node>();
		variables = new Hashtable<String, Node>();
		operations = new Hashtable<String, Node>();
		seenMachines = new Hashtable<String, AIdentifierExpression>();

		this.machineContextsTable = new Hashtable<String, MachineContext>();
		start.apply(this);
	}

	public String getName() {
		return machineName;
	}

	public Start getTree() {
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

	public Hashtable<Node, Node> getReferences() {
		return referencesTable;
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
			PMachineClauseComparator comperator = new PMachineClauseComparator();
			// Sort the machine clauses: declarations clauses first, then
			// properties clauses
			Collections.sort(copy, comperator);
			for (PMachineClause e : copy) {
				e.apply(this);
			}
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

	// TODO import, include, ..

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

	/**
	 * check identifier scope in properties clauses
	 */

	private void putLocalVariableIntoCurrentScope(AIdentifierExpression node)
			throws ScopeException {
		String name = Utils.getIdentifierAsString(node.getIdentifier());
		Hashtable<String, Node> currentScope = contextTable.get(contextTable
				.size() - 1);
		if (currentScope.containsKey(name)) {
			throw new ScopeException("Duplicate Identifier: " + name);
		} else {
			currentScope.put(name, node);
		}
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		String name = Utils.getIdentifierAsString(node.getIdentifier());
		for (int i = contextTable.size() - 1; i >= 0; i--) {
			Hashtable<String, Node> currentScope = contextTable.get(i);
			if (currentScope.containsKey(name)) {
				this.referencesTable.put(node, currentScope.get(name));
				return;
			}
		}
		throw new ScopeException("Unkown Identifier: '" + name
				+ "' at position: " + node.getStartPos());
	}

	private ArrayList<MachineContext> lookupExtendedMachines() {
		ArrayList<MachineContext> list = new ArrayList<MachineContext>();
		for (String s : seenMachines.keySet()) {
			AIdentifierExpression i = seenMachines.get(s);
			if (i.getIdentifier().size() == 1) {
				list.add(machineContextsTable.get(s));
			}
		}
		list.add(this);
		return list;
	}

	@Override
	public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();
		this.contextTable.add(this.getMachineParameters());
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {

		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			contextTable.add(s.getDeferredSets());
			contextTable.add(s.getEnumeratedSets());
			contextTable.add(s.getEnumValues());
			contextTable.add(s.getConstants());
		}

		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			this.contextTable.add(s.getMachineParameters());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getVariables());
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);

			this.contextTable.add(s.getMachineParameters());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getVariables());
		}
		if (node.getSubstitutions() != null) {
			node.getSubstitutions().apply(this);
		}
	}

	@Override
	public void caseAOperationsMachineClause(AOperationsMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			this.contextTable.add(s.getMachineParameters());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getVariables());
		}

		List<POperation> copy = new ArrayList<POperation>(node.getOperations());

		// first collect all operations
		for (POperation e : copy) {
			AOperation op = (AOperation) e;
			exist(op.getOpName());
			String name = Utils.getIdentifierAsString(op.getOpName());
			operations.put(name, op);
		}

		// visit all operations
		for (POperation e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAOperation(AOperation node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getReturnValues());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getOperationBody() != null) {
			node.getOperationBody().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		// TODO maybe give better feedback to the user, e.g. can not assign a
		// value to constant 'c'
		ArrayList<Hashtable<String, Node>> temp = contextTable;
		{
			contextTable = new ArrayList<Hashtable<String, Node>>();
			contextTable.add(variables);
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getLhsExpression());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		{
			contextTable = temp;
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getRhsExpressions());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
	}

	@Override
	public void caseAOpSubstitution(AOpSubstitution node) {
		if (node.getName() != null) {
			AIdentifierExpression op = (AIdentifierExpression) node.getName();
			String name = Utils.getIdentifierAsString(op.getIdentifier());
			Node o = operations.get(name); // TODO operation
											// of an
											// external
			// machine
			if (o != null) {
				this.referencesTable.put(op, o);
			} else {
				throw new ScopeException("Unknown operation '" + name + "'");
			}
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
	}

	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getImplication() != null) {
			node.getImplication().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		node.getPredicate().apply(this);
		node.getExpression().apply(this);
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		node.getPredicates().apply(this);
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAGeneralProductExpression(AGeneralProductExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		contextTable.add(new Hashtable<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		contextTable.remove(contextTable.size() - 1);
	}

}
