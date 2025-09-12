package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;

/**
 * A BDefinitions can depend on another BDefinitions. For the translation to
 * TLA+ the definitions must be sorted.
 * 
 * @author hansen
 */
public class DefinitionsSorter extends DepthFirstAdapter {
	private final MachineContext machineContext;
	private final Map<Node, Set<Node>> dependenciesMap;
	private Set<Node> current;

	private final List<PDefinition> allDefinitions;

	public List<PDefinition> getAllDefinitions() {
		return allDefinitions;
	}

	public DefinitionsSorter(MachineContext machineContext, List<PDefinition> allDefinitions) {
		this.machineContext = machineContext;
		this.dependenciesMap = new HashMap<>();

		allDefinitions.forEach(def -> def.apply(this));
		this.allDefinitions = sort(new ArrayList<>(allDefinitions));
	}

	private List<PDefinition> sort(List<PDefinition> list) {
		List<PDefinition> result = new ArrayList<>();
		boolean newRun = true;
		while (newRun) {
			newRun = false;
			for (PDefinition def : list) {
				if (result.contains(def))
					continue;
				Set<Node> set = dependenciesMap.get(def);
				if (set.isEmpty()) {
					newRun = true;
					result.add(def);

					Node defRef = machineContext.getReferences().get(def);
					if (null != defRef) {
						/*
						 * In this case the definition def is a constant
						 * assignment and reference node of the definition is
						 * the constant itself.
						 */
						removeDef(defRef);
					} else {
						removeDef(def);
					}
					break;
				}
			}
		}

		if (result.size() != list.size()) {
			throw new RuntimeException("Found cyclic Definitions.");
		}
		return result;
	}

	private void removeDef(Node def) {
		dependenciesMap.values().forEach(nodes -> nodes.remove(def));
	}

	private void startDefinition() {
		current = new HashSet<>();
	}

	private void endDefinition(Node def) {
		dependenciesMap.put(def, current);
		current = null;
	}

	public void inAExpressionDefinitionDefinition(AExpressionDefinitionDefinition node) {
		startDefinition();
	}

	public void outAExpressionDefinitionDefinition(AExpressionDefinitionDefinition node) {
		endDefinition(node);
	}

	public void inAPredicateDefinitionDefinition(APredicateDefinitionDefinition node) {
		startDefinition();
	}

	public void outAPredicateDefinitionDefinition(APredicateDefinitionDefinition node) {
		endDefinition(node);
	}

	public void inASubstitutionDefinitionDefinition(ASubstitutionDefinitionDefinition node) {
		startDefinition();
	}

	public void outASubstitutionDefinitionDefinition(ASubstitutionDefinitionDefinition node) {
		endDefinition(node);
	}

	public void inADefinitionExpression(ADefinitionExpression node) {
		Node refNode = machineContext.getReferences().get(node);
		// If refNode is null, then the whole branch was cloned when a constant assignment was generated
		if (null != refNode) {
			current.add(refNode);
		}
	}

	public void inAIdentifierExpression(AIdentifierExpression node) {
		Node identifierRef = machineContext.getReferences().get(node);
		if (identifierRef == null)
			return;

		if (machineContext.getConstants().containsValue(identifierRef)) {
			//current.add(identifierRef);
			return;
		}

		if (machineContext.getReferences().get(identifierRef) instanceof PDefinition) {
			current.add(identifierRef);
		}
	}
}
