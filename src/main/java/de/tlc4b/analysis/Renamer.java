package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALetSubstitution;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AVarSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;

public class Renamer extends DepthFirstAdapter {
	private final MachineContext machineContext;
	private final Hashtable<Node, String> namesTable;
	private final HashSet<String> globalNames;
	private final static Set<String> KEYWORDS = new HashSet<String>();
	static {
		KEYWORDS.add("ASSUME");
		KEYWORDS.add("ASSUMPTION");
		KEYWORDS.add("AXIOM");
		KEYWORDS.add("CASE");
		KEYWORDS.add("CHOOSE");
		KEYWORDS.add("CONSTANT");
		KEYWORDS.add("CONSTANTS");
		KEYWORDS.add("DOMAIN");
		KEYWORDS.add("ELSE");
		KEYWORDS.add("ENABLED");
		KEYWORDS.add("EXCEPT");
		KEYWORDS.add("EXTENDS");
		KEYWORDS.add("IF");
		KEYWORDS.add("IN");
		KEYWORDS.add("INSTANCE");
		KEYWORDS.add("LET");
		KEYWORDS.add("LOCAL");
		KEYWORDS.add("MODULE");
		KEYWORDS.add("OTHER");
		KEYWORDS.add("SF_");
		KEYWORDS.add("SUBSET");
		KEYWORDS.add("THEN");
		KEYWORDS.add("THEOREM");
		KEYWORDS.add("UNCHANGED");
		KEYWORDS.add("UNION");
		KEYWORDS.add("VARIABLE");
		KEYWORDS.add("VARIABLES");
		KEYWORDS.add("WF_");
		KEYWORDS.add("WITH");
		KEYWORDS.add("STATE");

		KEYWORDS.add("Init");
		KEYWORDS.add("Next");
		KEYWORDS.add("INVARIANT");

		KEYWORDS.add("Nat");
		KEYWORDS.add("Int");
		KEYWORDS.add("Seq");
	}
	private final static Set<String> RelationsKeywords = new HashSet<String>();
	static {
		RelationsKeywords.add("domain");
		RelationsKeywords.add("range");
		RelationsKeywords.add("id");
		RelationsKeywords.add("set_of_relations");
		RelationsKeywords.add("domain_restriction");
		RelationsKeywords.add("domain_substraction");
		RelationsKeywords.add("rel_inverse");
		RelationsKeywords.add("relational_image");
		RelationsKeywords.add("relational_overriding");
		RelationsKeywords.add("direct");
		RelationsKeywords.add("Seq");

	}

	private final static Set<String> SequencesKeywords = new HashSet<String>();
	static {
		SequencesKeywords.add("Seq");
		SequencesKeywords.add("Len");
		SequencesKeywords.add("Append");
		SequencesKeywords.add("Head");
		SequencesKeywords.add("Tail");
		SequencesKeywords.add("Subseq");
		SequencesKeywords.add("SelectSeq");
	}

	public Renamer(MachineContext machineContext) {
		this.machineContext = machineContext;
		this.namesTable = new Hashtable<Node, String>();
		this.globalNames = new HashSet<String>();
		start();

	}

	public void start() {
		evalGlobalNames(machineContext.getDeferredSets());
		evalGlobalNames(machineContext.getEnumeratedSets());
		evalEnumValues();
		evalGlobalNames(machineContext.getConstants());
		evalGlobalNames(machineContext.getVariables());
		evalGlobalNames(machineContext.getOperations());

		evalDefinitions();

		machineContext.getTree().apply(this);
	}

	private void evalEnumValues() {

		for (Entry<String, Node> entry : machineContext.getEnumValues()
				.entrySet()) {
			String name = entry.getKey();
			Node node = entry.getValue();

			if (name.indexOf('_') == 1) {
				name = name.replaceFirst("_", "1_");
			}
			String newName = incName(name);

			namesTable.put(node, newName);
			globalNames.add(newName);
		}
	}

	public void evalGlobalNames(LinkedHashMap<String, Node> map) {
		for (Entry<String, Node> entry : map.entrySet()) {
			String name = entry.getKey();
			String newName = incName(name);
			namesTable.put(map.get(name), newName);
			globalNames.add(newName);
		}
	}

	private void evalDefinitions() {
		ADefinitionsMachineClause node = machineContext
				.getDefinitionMachineClause();
		if (null == node) {
			return;
		}

		List<PDefinition> copy = new ArrayList<PDefinition>(
				node.getDefinitions());
		for (PDefinition e : copy) {
			String name = null;
			if (e instanceof AExpressionDefinitionDefinition) {
				name = ((AExpressionDefinitionDefinition) e).getName()
						.getText();
			} else if (e instanceof APredicateDefinitionDefinition) {
				name = ((APredicateDefinitionDefinition) e).getName().getText();
			} else if (e instanceof ASubstitutionDefinitionDefinition) {
				name = ((ASubstitutionDefinitionDefinition) e).getName()
						.getText();
			}
			String newName = incName(name);
			namesTable.put(e, newName);
			globalNames.add(newName);
		}

		for (PDefinition e : copy) {
			e.apply(this);
		}
	}

	public String getNameOfRef(Node node) {
		Node refNode = machineContext.getReferences().get(node);
		if (refNode == null) {
			refNode = node;
		}
		return namesTable.get(refNode);
	}

	public String getName(Node node) {
		return namesTable.get(node);
	}

	private String incName(String name) {
		String res = name;
		for (int i = 1; exist(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	private ArrayList<HashSet<String>> localContexts = new ArrayList<HashSet<String>>();

	private boolean exist(String name) {
		if (KEYWORDS.contains(name))
			return true;
		if (globalNames.contains(name))
			return true;
		// TODO check only if the standard module is extended

		if (StandardMadules.functions.contains(name))
			return true;
		if (SequencesKeywords.contains(name))
			return true;
		if (StandardMadules.SequencesExtendedKeywords.contains(name))
			return true;

		for (int i = 0; i < localContexts.size(); i++) {
			if (localContexts.get(i).contains(name))
				return true;
		}

		return false;
	}

	private String renameIdentifier(Node node) {
		AIdentifierExpression id = (AIdentifierExpression) node;
		String name = Utils.getIdentifierAsString(id.getIdentifier());
		String newName = incName(name);
		namesTable.put(id, newName);
		return newName;
	}

	private void evalDefinition(List<PExpression> params) {
		for (PExpression e : params) {
			renameIdentifier(e);
		}
	}

	@Override
	public void inAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		evalDefinition(node.getParameters());
	}

	@Override
	public void inAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		evalDefinition(node.getParameters());
	}

	@Override
	public void inASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		evalDefinition(node.getParameters());
	}

	// local variables

	@Override
	public void caseAForallPredicate(AForallPredicate node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getImplication().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicate().apply(this);
		removeLastContext();
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicate().apply(this);
		node.getExpression().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicates().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			e.apply(this);
		}
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAGeneralProductExpression(AGeneralProductExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
		node.getPredicates().apply(this);
		node.getExpression().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAOperation(AOperation node) {
		List<PExpression> list = new ArrayList<PExpression>();
		list.addAll(node.getParameters());
		list.addAll(node.getReturnValues());
		evalBoundedVariables(node, list);
		node.getOperationBody().apply(this);
		removeLastContext();
	}

	private void evalBoundedVariables(Node node, List<PExpression> params) {
		HashSet<String> context = new HashSet<String>();
		for (PExpression e : params) {
			String newName = renameIdentifier(e);
			context.add(newName);
		}
		localContexts.add(context);
	}

	@Override
	public void caseAAnySubstitution(AAnySubstitution node) {
		List<PExpression> list = new ArrayList<PExpression>();
		list.addAll(node.getIdentifiers());
		evalBoundedVariables(node, list);

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			e.apply(this);
		}
		node.getWhere().apply(this);
		node.getThen().apply(this);
		removeLastContext();
	}

	@Override
	public void caseALetSubstitution(ALetSubstitution node) {
		List<PExpression> list = new ArrayList<PExpression>();
		list.addAll(node.getIdentifiers());
		evalBoundedVariables(node, list);

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			e.apply(this);
		}
		node.getPredicate().apply(this);
		node.getSubstitution().apply(this);
		removeLastContext();
	}

	@Override
	public void caseAVarSubstitution(AVarSubstitution node) {
		List<PExpression> list = new ArrayList<PExpression>();
		list.addAll(node.getIdentifiers());
		evalBoundedVariables(node, list);
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			e.apply(this);
		}
		node.getSubstitution().apply(this);
		removeLastContext();
	}

	public void removeLastContext() {
		localContexts.remove(localContexts.size() - 1);
	}

}
