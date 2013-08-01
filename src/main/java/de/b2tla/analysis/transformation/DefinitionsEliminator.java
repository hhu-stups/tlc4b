package de.b2tla.analysis.transformation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADefinitionSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.Start;

/**
 * This class eliminates all definition calls in the MACHINE. A definition call
 * will be replaced by the right-hand side of the definition and all parameter
 * on the RHS are replaced by the arguments of the call.
 * 
 * Note: All parameters of a definition are replaced before calls of
 * sub-definitions are resolved. This behavior is similar to what ProB does by
 * eliminating all definitions.
 * 
 */
public class DefinitionsEliminator extends DepthFirstAdapter {

	private Hashtable<String, PDefinition> definitionsTable;
	private ArrayList<Hashtable<String, PExpression>> contextStack;

	public DefinitionsEliminator(Start node) {
		DefinitionCollector collector = new DefinitionCollector(node);
		definitionsTable = collector.getDefinitions();
		contextStack = new ArrayList<Hashtable<String, PExpression>>();
		node.apply(this);
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		List<PMachineClause> copy = node.getMachineClauses();
		ADefinitionsMachineClause defClause = null;
		for (PMachineClause e : copy) {
			e.apply(this);
			if (e instanceof ADefinitionsMachineClause) {
				defClause = (ADefinitionsMachineClause) e;
			}
		}
		if (defClause != null && defClause.getDefinitions().size() == 0) {
			defClause.replaceBy(null);
		}
	}

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
		List<PDefinition> copy = new ArrayList<PDefinition>(
				node.getDefinitions());
		for (PDefinition e : copy) {
			e.apply(this);
		}
		for (PDefinition e : copy) {
			if (e instanceof AExpressionDefinitionDefinition) {
				String name = ((AExpressionDefinitionDefinition) e).getName()
						.getText().toString();
				if (name.startsWith("ASSERT_LTL") || name.startsWith("scope_")|| name.startsWith("SET_PREF_"))
					continue;
			} else if (e instanceof APredicateDefinitionDefinition) {
				String name = ((APredicateDefinitionDefinition) e).getName().getText().toString();
				if (name.equals("GOAL"))
					continue;
			}
			e.replaceBy(null);
		}
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		String name = node.getDefLiteral().getText();
		PDefinition def = definitionsTable.get(name);

		ASubstitutionDefinitionDefinition clone = (ASubstitutionDefinitionDefinition) def
				.clone();
		Hashtable<String, PExpression> context = new Hashtable<String, PExpression>();
		ArrayList<PExpression> arguments = new ArrayList<PExpression>(
				node.getParameters());
		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone
					.getParameters().get(i);
			String paramName = Utils.getIdentifierAsString(p.getIdentifier());
			context.put(paramName, arguments.get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionExpression(ADefinitionExpression node) {
		String name = node.getDefLiteral().getText();
		PDefinition def = definitionsTable.get(name);

		AExpressionDefinitionDefinition clone = (AExpressionDefinitionDefinition) def
				.clone();
		Hashtable<String, PExpression> context = new Hashtable<String, PExpression>();
		ArrayList<PExpression> arguments = new ArrayList<PExpression>(
				node.getParameters());
		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone
					.getParameters().get(i);
			String paramName = Utils.getIdentifierAsString(p.getIdentifier());
			context.put(paramName, arguments.get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		String name = node.getDefLiteral().getText();
		PDefinition def = definitionsTable.get(name);

		APredicateDefinitionDefinition clone = (APredicateDefinitionDefinition) def
				.clone();
		Hashtable<String, PExpression> context = new Hashtable<String, PExpression>();
		ArrayList<PExpression> arguments = new ArrayList<PExpression>(
				node.getParameters());
		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone
					.getParameters().get(i);
			String paramName = Utils.getIdentifierAsString(p.getIdentifier());
			context.put(paramName, arguments.get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);

		node.replaceBy(clone.getRhs());

		contextStack.remove(context);
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (contextStack.size() == 0)
			return;
		String name = Utils.getIdentifierAsString(node.getIdentifier());

		for (int i = contextStack.size() - 1; i >= 0; i--) {
			Hashtable<String, PExpression> context = contextStack.get(i);
			PExpression e = context.get(name);
			if (e != null) {
				node.replaceBy((PExpression) e.clone());
			}
		}
	}

}
