package analysis;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
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
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import exceptions.ScopeException;

public class ScopeChecker extends DepthFirstAdapter {

	private final Hashtable<Node, Node> referencesTable;

	private ArrayList<Hashtable<String, Node>> contextTable;

	private final Hashtable<String, MachineDeclarationsCollector> scopeTable;

	private final MachineDeclarationsCollector declarations;

	public Hashtable<Node, Node> getReferencesTable() {
		return referencesTable;
	}

	public ScopeChecker(MachineDeclarationsCollector c,
			Hashtable<String, MachineDeclarationsCollector> table) {

		declarations = c;

		if (table == null)
			scopeTable = new Hashtable<String, MachineDeclarationsCollector>();
		else
			scopeTable = table;

		referencesTable = new Hashtable<Node, Node>();

		c.getTree().apply(this);
	}

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
		lookupIdentifier(node);

	}

	private void lookupIdentifier(AIdentifierExpression node) {
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

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		inAAbstractMachineParseUnit(node);
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
		outAAbstractMachineParseUnit(node);
	}

	@Override
	public void caseAMachineHeader(AMachineHeader node) {
	}

	@Override
	public void caseASeesMachineClause(ASeesMachineClause node) {
	}

	@Override
	public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();
		this.contextTable.add(declarations.getMachineParameters());
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
	}

	private ArrayList<MachineDeclarationsCollector> lookupExtendedMachines() {
		ArrayList<MachineDeclarationsCollector> list = new ArrayList<MachineDeclarationsCollector>();
		for (String s : declarations.getSeenMachines().keySet()) {
			AIdentifierExpression i = declarations.getSeenMachines().get(s);
			if (i.getIdentifier().size() == 1) {
				list.add(scopeTable.get(s));
			}
		}
		list.add(declarations);
		return list;
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {

		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineDeclarationsCollector> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineDeclarationsCollector s = list.get(i);
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
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		this.contextTable = new ArrayList<Hashtable<String, Node>>();

		ArrayList<MachineDeclarationsCollector> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineDeclarationsCollector s = list.get(i);
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

		ArrayList<MachineDeclarationsCollector> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineDeclarationsCollector s = list.get(i);

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

		ArrayList<MachineDeclarationsCollector> list = lookupExtendedMachines();
		for (int i = 0; i < list.size(); i++) {
			MachineDeclarationsCollector s = list.get(i);
			this.contextTable.add(s.getMachineParameters());
			this.contextTable.add(s.getDeferredSets());
			this.contextTable.add(s.getEnumeratedSets());
			this.contextTable.add(s.getEnumValues());
			this.contextTable.add(s.getConstants());
			this.contextTable.add(s.getVariables());
		}

		List<POperation> copy = new ArrayList<POperation>(node.getOperations());
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
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getOpName());
			for (TIdentifierLiteral e : copy) {
				e.apply(this);
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
			contextTable.add(declarations.getVariables());
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
			Node o = declarations.getOperations().get(name); // TODO operation
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
		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
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
