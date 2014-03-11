package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

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

public class DefinitionsOrder extends DepthFirstAdapter {
	private MachineContext machineContext;
	private Hashtable<Node, HashSet<Node>> dependenciesTable;
	private HashSet<Node> current;

	private ArrayList<PDefinition> allDefinitions;

	public ArrayList<PDefinition> getAllDefinitions() {
		return allDefinitions;
	}

	public DefinitionsOrder(MachineContext machineContext,
			ArrayList<PDefinition> allDefinitions) {
		this.machineContext = machineContext;
		dependenciesTable = new Hashtable<Node, HashSet<Node>>();

		for (PDefinition def : allDefinitions) {
			def.apply(this);
		}

		this.allDefinitions = sort(new ArrayList<PDefinition>(allDefinitions));

	}

	private ArrayList<PDefinition> sort(ArrayList<PDefinition> list) {
		ArrayList<PDefinition> result = new ArrayList<PDefinition>();
		boolean newRun = true;
		while (newRun) {
			newRun = false;
			Iterator<PDefinition> itr = list.iterator();
			while (itr.hasNext()) {
				PDefinition def = itr.next();
				if (result.contains(def))
					continue;
				HashSet<Node> set = dependenciesTable.get(def);
				if (set.size() == 0) {
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
		Iterator<HashSet<Node>> itr = dependenciesTable.values().iterator();
		while (itr.hasNext()) {
			itr.next().remove(def);
		}
	}

	public void inAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		current = new HashSet<Node>();
	}

	public void outAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		dependenciesTable.put(node, current);
		current = null;
	}

	public void inAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		current = new HashSet<Node>();
	}

	public void outAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		dependenciesTable.put(node, current);
		current = null;
	}

	public void inASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		current = new HashSet<Node>();
	}

	public void outASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		dependenciesTable.put(node, current);
		current = null;
	}

	public void inADefinitionExpression(ADefinitionExpression node) {

		Node refNode = machineContext.getReferences().get(node);
		/*
		 * If refNode is null, then the whole branch was cloned when a constant
		 * assignment was generated
		 */

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
