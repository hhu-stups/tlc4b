package de.tlc4b.analysis.transformation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
 */
public class DefinitionsEliminator extends DepthFirstAdapter {

	private final IDefinitions definitions = new Definitions();
	private final List<Map<String, PExpression>> contextStack = new ArrayList<>();

	public static void eliminateDefinitions(Start start){
		start.apply(new DefinitionsEliminator(start));
	}
	
	private DefinitionsEliminator(Start node) {
		new DefinitionCollector(definitions).collectDefinitions(node);
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

		ASubstitutionDefinitionDefinition clone = (ASubstitutionDefinitionDefinition) definitions.getDefinition(name).clone();
		Map<String, PExpression> context = new HashMap<>();
		handleParameters(new LinkedList<>(node.getParameters()), clone.getParameters(), context);

		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionExpression(ADefinitionExpression node) {
		String name = node.getDefLiteral().getText();
		if (checkExternalFunction(name, new ArrayList<>(node.getParameters())))
			return;

		AExpressionDefinitionDefinition clone = (AExpressionDefinitionDefinition) definitions.getDefinition(name).clone();
		Map<String, PExpression> context = new HashMap<>();
		handleParameters(new LinkedList<>(node.getParameters()), clone.getParameters(), context);

		contextStack.add(context);
		clone.getRhs().apply(this);
		node.replaceBy(clone.getRhs());
		contextStack.remove(context);
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		String name = node.getDefLiteral().getText();
		if (checkExternalFunction(name, new ArrayList<>(node.getParameters())))
			return;

		APredicateDefinitionDefinition clone = (APredicateDefinitionDefinition) definitions.getDefinition(name).clone();
		Map<String, PExpression> context = new HashMap<>();
		handleParameters(new LinkedList<>(node.getParameters()), clone.getParameters(), context);

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
			PExpression e = contextStack.get(i).get(name);
			if (e != null) {
				node.replaceBy(e.clone());
			}
		}
	}

	private boolean checkExternalFunction(String name, List<PExpression> arguments) {
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			for (PExpression arg : arguments) {
				arg.apply(this);
			}
			return true;
		}
		return false;
	}

	private void handleParameters(List<PExpression> arguments, List<PExpression> cloneArguments, Map<String, PExpression> context) {
		for (int i = 0; i < cloneArguments.size(); i++) {
			arguments.get(i).apply(this);
			AIdentifierExpression param = (AIdentifierExpression) cloneArguments.get(i);
			context.put(Utils.getTIdentifierListAsString(param.getIdentifier()), arguments.get(i));
		}
	}
}
