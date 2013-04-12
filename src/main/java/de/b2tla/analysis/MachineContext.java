package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.b2tla.exceptions.ScopeException;
import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConcreteVariablesMachineClause;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADeferredSetSet;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADefinitionSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
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
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.ARecordFieldExpression;
import de.be4.classicalb.core.parser.node.ASeesMachineClause;
import de.be4.classicalb.core.parser.node.ASetsContextClause;
import de.be4.classicalb.core.parser.node.ASetsMachineClause;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.PMachineHeader;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.PSet;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class MachineContext extends DepthFirstAdapter {

	private String machineName;
	private PMachineHeader header;
	private final Start start;
	private final Hashtable<String, MachineContext> machineContextsTable;

	// machine identifier
	private final LinkedHashMap<String, Node> setParameter;
	private final LinkedHashMap<String, Node> scalarParameter;

	private final LinkedHashMap<String, Node> deferredSets;
	private final LinkedHashMap<String, Node> enumeratedSets;
	private final LinkedHashMap<String, Node> enumValues;
	private final LinkedHashMap<String, Node> constants;
	private final LinkedHashMap<String, Node> variables;
	private final LinkedHashMap<String, Node> definitions;
	private final LinkedHashMap<String, Node> operations;
	private final LinkedHashMap<String, AIdentifierExpression> seenMachines;

	// machine clauses
	private AConstraintsMachineClause constraintMachineClause;
	private ASeesMachineClause seesMachineClause;
	private ASetsContextClause setsMachineClause; // TODO
	private AConstantsMachineClause constantsMachineClause;
	private ADefinitionsMachineClause definitionMachineClause;
	private APropertiesMachineClause propertiesMachineClause;
	private AVariablesMachineClause variablesMachineClause;
	private AInvariantMachineClause invariantMachineClause;
	private AInitialisationMachineClause initialisationMachineClause;
	private AOperationsMachineClause operationMachineClause;
	private AAssertionsMachineClause assertionMachineClause;

	private ArrayList<LinkedHashMap<String, Node>> contextTable;

	private final Hashtable<Node, Node> referencesTable;

	public MachineContext(Start start,
			Hashtable<String, MachineContext> machineContextsTable) {
		this.start = start;
		this.referencesTable = new Hashtable<Node, Node>();

		this.setParameter = new LinkedHashMap<String, Node>();
		this.scalarParameter = new LinkedHashMap<String, Node>();

		this.deferredSets = new LinkedHashMap<String, Node>();
		this.enumeratedSets = new LinkedHashMap<String, Node>();
		this.enumValues = new LinkedHashMap<String, Node>();
		this.constants = new LinkedHashMap<String, Node>();
		this.definitions = new LinkedHashMap<String, Node>();
		this.variables = new LinkedHashMap<String, Node>();
		this.operations = new LinkedHashMap<String, Node>();
		this.seenMachines = new LinkedHashMap<String, AIdentifierExpression>();

		this.machineContextsTable = machineContextsTable;

		start.apply(this);
	}

	public MachineContext(Start start) {
		this.start = start;
		this.referencesTable = new Hashtable<Node, Node>();

		this.setParameter = new LinkedHashMap<String, Node>();
		this.scalarParameter = new LinkedHashMap<String, Node>();

		deferredSets = new LinkedHashMap<String, Node>();
		enumeratedSets = new LinkedHashMap<String, Node>();
		enumValues = new LinkedHashMap<String, Node>();
		constants = new LinkedHashMap<String, Node>();
		variables = new LinkedHashMap<String, Node>();
		this.definitions = new LinkedHashMap<String, Node>();
		operations = new LinkedHashMap<String, Node>();
		seenMachines = new LinkedHashMap<String, AIdentifierExpression>();

		this.machineContextsTable = new Hashtable<String, MachineContext>();
		start.apply(this);
	}

	private void exist(LinkedList<TIdentifierLiteral> list) {
		String name = Utils.getIdentifierAsString(list);
		existString(name);
	}

	private void existString(String name) {
		// TODO add all identifier to this
		if (constants.containsKey(name) || variables.containsKey(name)
				|| operations.containsKey(name)
				|| deferredSets.containsKey(name)
				|| enumeratedSets.containsKey(name)
				|| enumValues.containsKey(name)
				|| setParameter.containsKey(name)
				|| scalarParameter.containsKey(name)
				|| seenMachines.containsKey(name)
				|| definitions.containsKey(name)) {
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
		this.header = node;
		List<TIdentifierLiteral> nameList = new ArrayList<TIdentifierLiteral>(
				node.getName());
		machineName = Utils.getIdentifierAsString(nameList);

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		for (PExpression e : copy) {
			AIdentifierExpression p = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(p.getIdentifier());
			exist(p.getIdentifier());
			if (Character.isUpperCase(name.charAt(0))) {
				this.setParameter.put(name, p);
			} else {
				this.scalarParameter.put(name, p);
			}
		}
	}

	/**
	 * Definitions
	 */

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
		definitionMachineClause = node;
		List<PDefinition> copy = new ArrayList<PDefinition>(
				node.getDefinitions());

		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			contextTable.add(s.getDeferredSets());
			contextTable.add(s.getEnumeratedSets());
			contextTable.add(s.getEnumValues());
			contextTable.add(s.getConstants());
			contextTable.add(s.getVariables());
			contextTable.add(s.getDefinitions());
		}

		for (PDefinition e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		visitBDefinition(node, node.getName().getText().toString(),
				node.getParameters(), node.getRhs());
	}

	@Override
	public void caseAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		visitBDefinition(node, node.getName().getText().toString(),
				node.getParameters(), node.getRhs());
	}

	@Override
	// d == x := 1
	public void caseASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		visitBDefinition(node, node.getName().getText().toString(),
				node.getParameters(), node.getRhs());

	}

	public void visitBDefinition(Node node, String name,
			List<PExpression> copy, Node rightSide) {
		if (name.equals("ASSERT_LTL")) {
			return;
		}

		existString(name);
		definitions.put(name, node);

		contextTable.add(new LinkedHashMap<String, Node>());
		for (PExpression e : copy) {
			putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
		}

		rightSide.apply(this);

		contextTable.remove(contextTable.size() - 1);
	}

	@Override
	public void caseADefinitionExpression(ADefinitionExpression node) {
		visitBDefinitionCall(node, node.getDefLiteral().getText().toString(),
				node.getParameters());
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		visitBDefinitionCall(node, node.getDefLiteral().getText().toString(),
				node.getParameters());
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		visitBDefinitionCall(node, node.getDefLiteral().getText().toString(),
				node.getParameters());
	}

	private void visitBDefinitionCall(Node node, String name,
			List<PExpression> copy) {
		for (PExpression pExpression : copy) {
			pExpression.apply(this);
		}
		for (int i = contextTable.size() - 1; i >= 0; i--) {
			LinkedHashMap<String, Node> currentScope = contextTable.get(i);
			if (currentScope.containsKey(name)) {
				this.referencesTable.put(node, currentScope.get(name));
				return;
			}
		}
		throw new ScopeException("Unkown definition: '" + name
				+ "' at position: " + node.getStartPos());
	}

	@Override
	public void caseASeesMachineClause(ASeesMachineClause node) {
		this.seesMachineClause = node;
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
	public void caseASetsContextClause(ASetsContextClause node) {
		this.setsMachineClause = node;
		List<PSet> copy = new ArrayList<PSet>(node.getSet());
		for (PSet e : copy) {
			e.apply(this);
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
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		this.constantsMachineClause = node;
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
		this.variablesMachineClause = node;
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(v.getIdentifier());
			exist(v.getIdentifier());
			variables.put(name, v);
		}
	}

	private void putLocalVariableIntoCurrentScope(AIdentifierExpression node)
			throws ScopeException {
		String name = Utils.getIdentifierAsString(node.getIdentifier());
		LinkedHashMap<String, Node> currentScope = contextTable
				.get(contextTable.size() - 1);
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
			LinkedHashMap<String, Node> currentScope = contextTable.get(i);
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
		this.constraintMachineClause = node;

		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();
		this.contextTable.add(this.scalarParameter);
		this.contextTable.add(this.setParameter);
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		this.propertiesMachineClause = node;

		/**
		 * check identifier scope in properties clauses
		 */

		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			contextTable.add(s.getDeferredSets());
			contextTable.add(s.getEnumeratedSets());
			contextTable.add(s.getEnumValues());
			contextTable.add(s.getConstants());
			contextTable.add(s.getDefinitions());
		}

		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		this.invariantMachineClause = node;

		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			this.contextTable.add(s.getSetParamter());
			this.contextTable.add(s.getScalarParameter());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getDefinitions());
			this.contextTable.add(s.getVariables());
		}
		node.getPredicates().apply(this);
	}

	@Override
	public void caseAAssertionsMachineClause(AAssertionsMachineClause node) {
		this.assertionMachineClause = node;
		
		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();
		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			this.contextTable.add(s.getSetParamter());
			this.contextTable.add(s.getScalarParameter());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getDefinitions());
			this.contextTable.add(s.getVariables());
		}
		
		List<PPredicate> copy = new ArrayList<PPredicate>(node.getPredicates());
		for (PPredicate e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		this.initialisationMachineClause = node;

		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();

		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);

			this.contextTable.add(s.getSetParamter());
			this.contextTable.add(s.getScalarParameter());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getDefinitions());
			this.contextTable.add(s.getVariables());
		}
		if (node.getSubstitutions() != null) {
			node.getSubstitutions().apply(this);
		}
	}

	@Override
	public void caseAOperationsMachineClause(AOperationsMachineClause node) {
		this.operationMachineClause = node;
		this.contextTable = new ArrayList<LinkedHashMap<String, Node>>();
		ArrayList<MachineContext> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineContext s = list.get(i);
			this.contextTable.add(s.getSetParamter());
			this.contextTable.add(s.getScalarParameter());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getDefinitions());
			this.contextTable.add(s.getVariables());
		}
		List<POperation> copy = new ArrayList<POperation>(node.getOperations());
		// first collect all operations
		for (POperation e : copy) {
			AOperation op = (AOperation) e;
			///exist(op.getOpName());
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
		contextTable.add(new LinkedHashMap<String, Node>());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getReturnValues());
			for (PExpression e : copy) {
				AIdentifierExpression id = (AIdentifierExpression) e;
				exist(id.getIdentifier());
				putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
			}
		}

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				AIdentifierExpression id = (AIdentifierExpression) e;
				exist(id.getIdentifier());
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
		ArrayList<LinkedHashMap<String, Node>> temp = contextTable;
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getLhsExpression());
			ArrayList<LinkedHashMap<String, Node>> varTable = new ArrayList<LinkedHashMap<String, Node>>();
			varTable.add(variables);
			for (PExpression e : copy) {
				if (e instanceof AFunctionExpression) {
					contextTable = varTable;
					((AFunctionExpression) e).getIdentifier().apply(this);
					for (Node n : ((AFunctionExpression) e).getParameters()) {
						contextTable = temp;
						n.apply(this);
					}
				} else {
					contextTable = temp; // TODO outputparameter + variables
					e.apply(this);
				}
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
	public void caseAAnySubstitution(AAnySubstitution node) {
		contextTable.add(new LinkedHashMap<String, Node>());
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			putLocalVariableIntoCurrentScope((AIdentifierExpression) e);
		}
		node.getWhere().apply(this);
		node.getThen().apply(this);
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
		contextTable.add(new LinkedHashMap<String, Node>());
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
	public void caseARecEntry(ARecEntry node) {
		node.getValue().apply(this);
	}

	@Override
	public void caseARecordFieldExpression(ARecordFieldExpression node) {
		node.getRecord().apply(this);
	}

	public String getMachineName() {
		return machineName;
	}

	public PMachineHeader getHeader() {
		return header;
	}

	public Start getTree() {
		return start;
	}

	public LinkedHashMap<String, Node> getSetParamter() {
		return setParameter;
	}

	public LinkedHashMap<String, Node> getScalarParameter() {
		return scalarParameter;
	}

	public LinkedHashMap<String, Node> getConstants() {
		return constants;
	}

	public LinkedHashMap<String, Node> getDefinitions() {
		return definitions;
	}

	public LinkedHashMap<String, Node> getVariables() {
		return variables;
	}

	public LinkedHashMap<String, Node> getOperations() {
		return operations;
	}

	public LinkedHashMap<String, Node> getDeferredSets() {
		return deferredSets;
	}

	public LinkedHashMap<String, Node> getEnumeratedSets() {
		return enumeratedSets;
	}

	public LinkedHashMap<String, Node> getEnumValues() {
		return enumValues;
	}

	public LinkedHashMap<String, AIdentifierExpression> getSeenMachines() {
		return seenMachines;
	}

	public Hashtable<Node, Node> getReferences() {
		return referencesTable;
	}

	/*
	 * machine clauses getter
	 */

	public AConstraintsMachineClause getConstraintMachineClause() {
		return constraintMachineClause;
	}

	public ASeesMachineClause getSeesMachineClause() {
		return seesMachineClause;
	}

	public ASetsContextClause getSetsMachineClause() {
		return setsMachineClause;
	}

	public AConstantsMachineClause getConstantsMachineClause() {
		return constantsMachineClause;
	}

	public APropertiesMachineClause getPropertiesMachineClause() {
		return propertiesMachineClause;
	}

	public AVariablesMachineClause getVariablesMachineClause() {
		return variablesMachineClause;
	}

	public AInvariantMachineClause getInvariantMachineClause() {
		return invariantMachineClause;
	}

	public AInitialisationMachineClause getInitialisationMachineClause() {
		return initialisationMachineClause;
	}

	public AOperationsMachineClause getOperationMachineClause() {
		return operationMachineClause;
	}

	public ADefinitionsMachineClause getDefinitionMachineClause() {
		return definitionMachineClause;
	}

}

class PMachineClauseComparator implements Comparator<PMachineClause> {

	private static Hashtable<Object, Integer> priority = new Hashtable<Object, Integer>();
	static {
		// declarations clauses

		priority.put(ASeesMachineClause.class, 11);
		priority.put(ASetsMachineClause.class, 10);
		priority.put(AConstantsMachineClause.class, 9);
		priority.put(AVariablesMachineClause.class, 8);
		priority.put(AConcreteVariablesMachineClause.class, 7);
		priority.put(ADefinitionsMachineClause.class, 6);

		// properties clauses
		priority.put(AConstraintsMachineClause.class, 5);
		priority.put(APropertiesMachineClause.class, 4);
		priority.put(AInvariantMachineClause.class, 3);
		priority.put(AAssertionsMachineClause.class, 2);
		priority.put(AOperationsMachineClause.class, 1);
		priority.put(AInitialisationMachineClause.class, 0);
	}

	public int compare(PMachineClause arg0, PMachineClause arg1) {
		if (priority.get(arg0.getClass()).intValue() < priority.get(
				arg1.getClass()).intValue()) {
			return 1;
		}
		if (priority.get(arg0.getClass()).intValue() > priority.get(
				arg1.getClass()).intValue()) {
			return -1;
		}

		return 0;
	}

}
