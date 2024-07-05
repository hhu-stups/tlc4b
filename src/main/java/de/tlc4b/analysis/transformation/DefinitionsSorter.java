package de.tlc4b.analysis.transformation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADefinitionSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.PDefinition;

public class DefinitionsSorter extends DepthFirstAdapter {
	final LinkedHashMap<String, HashSet<String>> dependencies;
	final LinkedHashMap<String, HashSet<String>> allDependencies;
	final LinkedHashMap<String, PDefinition> definitionsTable;
	final ArrayList<PDefinition> res;
	String current = null;

	public DefinitionsSorter(ADefinitionsMachineClause clause) {
		dependencies = new LinkedHashMap<>();
		allDependencies = new LinkedHashMap<>();
		definitionsTable = new LinkedHashMap<>();
		res = new ArrayList<>();

		clause.apply(this);

		for (String defName : dependencies.keySet()) {
			resolveDependencies(defName);
		}

		ArrayList<String> defs = new ArrayList<>(allDependencies.keySet());
		
		
		while (!res.containsAll(definitionsTable.values())) {
			for (String next : new ArrayList<>(defs)) {
				HashSet<String> deps = allDependencies.get(next);

				deps.retainAll(defs);

				if (deps.isEmpty()) {
					PDefinition pDefinition = definitionsTable.get(next);
					pDefinition.replaceBy(null);
					res.add(pDefinition);
					defs.remove(next);
				}
			}
		}
		clause.setDefinitions(res);

	}

	private void resolveDependencies(String defName) {
		if (allDependencies.containsKey(defName)) {
			return;
		}
		HashSet<String> allDeps = new HashSet<>();
		HashSet<String> deps = dependencies.get(defName);
		for (String def : deps) {
			resolveDependencies(def);
			allDeps.add(def);
			allDeps.addAll(allDependencies.get(def));
		}
		allDependencies.put(defName, allDeps);

	}

	public static void sortDefinitions(ADefinitionsMachineClause clause) {
		new DefinitionsSorter(clause);

	}

	@Override
	public void inAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		String name = node.getName().getText();
		addDefinition(name);
		definitionsTable.put(name, node);
		current = name;
	}

	@Override
	public void inASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		String name = node.getName().getText();
		addDefinition(name);
		definitionsTable.put(name, node);
		current = name;
	}

	@Override
	public void inAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		String name = node.getName().getText();
		addDefinition(name);
		definitionsTable.put(name, node);
		current = name;
	}

	@Override
	public void inADefinitionExpression(ADefinitionExpression node) {
		String name = node.getDefLiteral().getText();
		addDefinitionCall(name);
	}

	@Override
	public void inADefinitionPredicate(ADefinitionPredicate node) {
		String name = node.getDefLiteral().getText();
		addDefinitionCall(name);
	}

	@Override
	public void inADefinitionSubstitution(ADefinitionSubstitution node) {
		String name = node.getDefLiteral().getText();
		addDefinitionCall(name);
	}

	private void addDefinition(String name) {
		if (!dependencies.containsKey(name)) {
			dependencies.put(name, new HashSet<>());
		}
	}

	private void addDefinitionCall(String name) {
		dependencies.get(current).add(name);
	}

}
