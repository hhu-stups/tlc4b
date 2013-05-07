package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.Node;
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
		RelationsKeywords.add("Seq");
		RelationsKeywords.add("Seq");
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
		eval(machineContext.getDeferredSets());
		eval(machineContext.getEnumeratedSets());
		eval(machineContext.getConstants());
		eval(machineContext.getVariables());
		eval(machineContext.getOperations());
		machineContext.getTree().apply(this);
	}

	public void eval(LinkedHashMap<String, Node> map) {
		Iterator<String> iter = map.keySet().iterator();
		while (iter.hasNext()) {
			String name = iter.next();
			String newName = incName(name);
			namesTable.put(map.get(name), newName);
			globalNames.add(newName);
		}
	}

	public String getName(Node node) {
		Node refNode = machineContext.getReferences().get(node);
		if (refNode == null) {
			refNode = node;
		}
		return namesTable.get(refNode);
	}

	private String getName(String name) {
		String res = name;
		for (int i = 1; KEYWORDS.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	private String incName(String name) {
		String res = name;
		for (int i = 1; exist(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	private boolean exist(String name) {
		if (KEYWORDS.contains(name))
			return true;
		if (globalNames.contains(name))
			return true;
		if (SequencesKeywords.contains(name))
			return true;

		return false;
	}

	private void renameIdentifier(Node node) {
		AIdentifierExpression id = (AIdentifierExpression) node;
		String name = Utils.getIdentifierAsString(id.getIdentifier());
		String newName = incName(name);
		namesTable.put(id, newName);
	}

	private void evalDefinition(Node node, String name, List<PExpression> params) {
		String newName = incName(name);
		namesTable.put(node, newName);
		for (PExpression e : params) {
			renameIdentifier(e);
		}
	}

	@Override
	public void inAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		evalDefinition(node, node.getName().getText(), node.getParameters());
	}

	@Override
	public void inAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		evalDefinition(node, node.getName().getText(), node.getParameters());
	}

	@Override
	public void inASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		evalDefinition(node, node.getName().getText(), node.getParameters());
	}

	public void inAForallPredicate(AForallPredicate node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAExistsPredicate(AExistsPredicate node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inALambdaExpression(ALambdaExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAComprehensionSetExpression(AComprehensionSetExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAGeneralProductExpression(AGeneralProductExpression node) {

		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAGeneralSumExpression(AGeneralSumExpression node) {
		evalBoundedVariables(node, node.getIdentifiers());
	}

	public void inAOperation(AOperation node) {
		evalBoundedVariables(node, node.getParameters());
		evalBoundedVariables(node, node.getReturnValues());
	}

	private void evalBoundedVariables(Node node, List<PExpression> params) {
		for (PExpression e : params) {
			renameIdentifier(e);
		}
	}

}
