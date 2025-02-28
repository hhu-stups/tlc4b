package de.tlc4b.analysis.transformation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.IDefinitions;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.analysis.checking.DefinitionCollector;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADefinitionSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.Utils;
import de.tlc4b.analysis.StandardModules;

/**
 * This class eliminates all definition calls in the MACHINE. A definition call
 * will be replaced by the right-hand side of the definition and all parameter
 * on the RHS are replaced by the arguments of the call.
 * <p>
 * Note: All parameters of a definition are replaced before a call of a
 * sub-definition is resolved. This behavior is similar to what ProB does when
 * eliminating all definitions.
 * 
 */
public class DefinitionsEliminator extends DepthFirstAdapter {

	private final IDefinitions definitions = new Definitions();
	private final ArrayList<Hashtable<String, PExpression>> contextStack;

	public static void eliminateDefinitions(Start start){
		new DefinitionsEliminator(start);
	}
	
	private DefinitionsEliminator(Start node) {
		new DefinitionCollector(definitions).collectDefinitions(node);
		contextStack = new ArrayList<>();
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
		if (defClause != null && defClause.getDefinitions().isEmpty()) {
			defClause.replaceBy(null);
		}
	}

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
		/*
		 * Definitions from other definitions files were injected into the
		 * DefinitionsCLause. However, their parent was not correctly set to the
		 * DefinitionsClause. Hence e.replaceBy(null) would not eliminate them.
		 * Therefore, we have to create a new list and have to the use the
		 * setDefinitions method form {link ADefinitionsMachineClause}.
		 */

		List<PDefinition> newDefinitionsList = new ArrayList<>();
		List<PDefinition> oldDefinitionsList = new ArrayList<>(node.getDefinitions());
		for (PDefinition e : oldDefinitionsList) {
			// replace all definitions calls inside the definitions bodies
			if (e instanceof AExpressionDefinitionDefinition) {
				String name = ((AExpressionDefinitionDefinition) e).getName().getText();
				if (Utils.isProBSpecialDefinitionName(name))
					continue;
			}
			e.apply(this);
		}

		// add certain definitions to the new definitions list in order to
		// obtain them for the translation
		for (PDefinition e : oldDefinitionsList) {
			if (e instanceof AExpressionDefinitionDefinition) {
				String name = ((AExpressionDefinitionDefinition) e).getName().getText();
				if (Utils.isProBSpecialDefinitionName(name)
						|| StandardModules.isKeywordInModuleExternalFunctions(name)) {
					newDefinitionsList.add(e);
				}
			} else if (e instanceof APredicateDefinitionDefinition) {
				String name = ((APredicateDefinitionDefinition) e).getName().getText();
				if (Utils.isProBSpecialDefinitionName(name)
						|| StandardModules.isKeywordInModuleExternalFunctions(name)) {
					newDefinitionsList.add(e);
				}
			}
		}
		for (PDefinition def : newDefinitionsList) {
			// we have deleted all parents of the definitions in order to set
			// them in the next step (seems to be a bug in SabbleCC)
			def.replaceBy(null);
		}
		node.setDefinitions(newDefinitionsList);
	}

	@Override
	public void caseADefinitionSubstitution(ADefinitionSubstitution node) {
		String name = node.getDefLiteral().getText();
		PDefinition def = definitions.getDefinition(name);

		ASubstitutionDefinitionDefinition clone = (ASubstitutionDefinitionDefinition) def.clone();
		Hashtable<String, PExpression> context = new Hashtable<>();
		ArrayList<PExpression> arguments = new ArrayList<>(node.getParameters());
		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone
					.getParameters().get(i);
			String paramName = Utils.getTIdentifierListAsString(p.getIdentifier());

			Node arg = arguments.get(i);
			arg.apply(this);
			context.put(paramName, node.getParameters().get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionExpression(ADefinitionExpression node) {
		String name = node.getDefLiteral().getText();
		ArrayList<PExpression> arguments = new ArrayList<>(node.getParameters());
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			for (PExpression arg : arguments) {
				arg.apply(this);
			}
			return;
		}

		PDefinition def = definitions.getDefinition(name);
		AExpressionDefinitionDefinition clone = (AExpressionDefinitionDefinition) def.clone();
		Hashtable<String, PExpression> context = new Hashtable<>();

		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone.getParameters().get(i);
			String paramName = Utils.getTIdentifierListAsString(p.getIdentifier());
			Node arg = arguments.get(i);
			arg.apply(this);
			context.put(paramName, node.getParameters().get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		String name = node.getDefLiteral().getText();
		PDefinition def = definitions.getDefinition(name);

		ArrayList<PExpression> arguments = new ArrayList<>(node.getParameters());
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			for (PExpression arg : arguments) {
				arg.apply(this);
			}
			return;
		}

		APredicateDefinitionDefinition clone = (APredicateDefinitionDefinition) def.clone();
		Hashtable<String, PExpression> context = new Hashtable<>();

		for (int i = 0; i < clone.getParameters().size(); i++) {
			AIdentifierExpression p = (AIdentifierExpression) clone.getParameters().get(i);
			String paramName = Utils.getTIdentifierListAsString(p.getIdentifier());

			Node arg = arguments.get(i);
			arg.apply(this);
			context.put(paramName, node.getParameters().get(i));
			// context.put(paramName, arguments.get(i));
		}
		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (contextStack.isEmpty())
			return;
		String name = Utils.getTIdentifierListAsString(node.getIdentifier());

		for (int i = contextStack.size() - 1; i >= 0; i--) {
			Hashtable<String, PExpression> context = contextStack.get(i);
			PExpression e = context.get(name);
			if (e != null) {
				node.replaceBy(e.clone());
			}
		}
	}

}
