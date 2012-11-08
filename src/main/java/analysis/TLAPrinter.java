package analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceSubstitution;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.AParallelSubstitution;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class TLAPrinter extends DepthFirstAdapter {

	private Hashtable<Node, Boolean> initialisationTable;

	private StringBuilder sb;

	public StringBuilder getStringbuilder() {
		return sb;
	}

	private MachineContext c;
	private Typechecker t;
	private UnchangedVariablesFinder u;
	private PrecedenceCollector p;

	public TLAPrinter(MachineContext c, Typechecker t,
			UnchangedVariablesFinder u, PrecedenceCollector p) {
		initialisationTable = new Hashtable<Node, Boolean>();
		this.c = c;
		this.t = t;
		this.u = u;
		this.p = p;

		sb = new StringBuilder();
		c.getTree().apply(this);
	}

	@Override
	public void defaultIn(final Node node) {
		if (p.getBrackets().contains(node)) {
			sb.append("(");
		}
	}

	@Override
	public void defaultOut(final Node node) {
		if (p.getBrackets().contains(node)) {
			sb.append(")");
		}
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		inAAbstractMachineParseUnit(node);
		if (node.getVariant() != null) {
			node.getVariant().apply(this);
		}

		sb.append("MODULE ");
		if (node.getHeader() != null) {
			node.getHeader().apply(this);
		}
		sb.append("\n");
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
		inAMachineHeader(node);
		sb.append(node);
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getName());
			for (TIdentifierLiteral e : copy) {
				e.apply(this);
			}
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outAMachineHeader(node);
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		inAConstantsMachineClause(node);
		sb.append("CONSTANTS ");
		for (Iterator<PExpression> itr = node.getIdentifiers().iterator(); itr
				.hasNext();) {
			PExpression e = itr.next();

			e.apply(this);

			if (itr.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append("\n");
		outAConstantsMachineClause(node);
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
		inAPropertiesMachineClause(node);
		sb.append("ASSUME ");
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		sb.append("\n");
		outAPropertiesMachineClause(node);
	}

	@Override
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
		inAVariablesMachineClause(node);
		sb.append("VARIABLES ");
		for (Iterator<PExpression> itr = node.getIdentifiers().iterator(); itr
				.hasNext();) {
			PExpression e = itr.next();

			e.apply(this);

			if (itr.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append("\n");
		outAVariablesMachineClause(node);
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		inAInvariantMachineClause(node);
		sb.append("Inv == ");
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		sb.append("\n");
		outAInvariantMachineClause(node);
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		sb.append("Init == ");
		initialisationTable.put(node.getSubstitutions(), true);
		node.getSubstitutions().apply(this);
		sb.append("\n");
	}

	/**
	 * Substitutions
	 * 
	 */

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		List<PExpression> copy2 = new ArrayList<PExpression>(
				node.getRhsExpressions());

		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (initialisationTable.get(node) == null) {
				sb.append("'");
			}
			sb.append(" = ");
			copy2.get(i).apply(this);

			if (i < copy.size() - 1) {
				sb.append(" /\\ ");
			}
		}

		unchangedVariables(node);

	}

	public void unchangedVariables(Node node) {
		if (initialisationTable.get(node) == null) {
			ArrayList<Node> unchangedVariables = new ArrayList<Node>(u
					.getUnchangedVariablesTable().get(node));
			if (unchangedVariables.size() > 0) {
				sb.append(" /\\ UNCHANGED <<");
				for (int i = 0; i < unchangedVariables.size(); i++) {
					unchangedVariables.get(i).apply(this);
					if (i < unchangedVariables.size() - 1) {
						sb.append(", ");
					}
				}
				sb.append(">>");
			}
		}
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());

		sb.append("(");
		for (int i = 0; i < copy.size(); i++) {
			copy.get(i).apply(this);
			if (i < copy.size() - 1) {
				sb.append(" \\/ ");
			}
		}
		sb.append(")");

		unchangedVariables(node);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		sb.append(" IF ");
		node.getCondition().apply(this);
		sb.append(" THEN ");
		node.getThen().apply(this);
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		sb.append(" ELSE ");
		node.getElse().apply(this);

		unchangedVariables(node);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		for (Iterator<PSubstitution> itr = node.getSubstitutions().iterator(); itr
				.hasNext();) {
			PSubstitution e = itr.next();

			e.apply(this);

			if (itr.hasNext()) {
				sb.append(" /\\ ");
			}
		}

		unchangedVariables(node);
	}

	@Override
	public void caseAOperationsMachineClause(AOperationsMachineClause node) {
		{
			List<POperation> copy = new ArrayList<POperation>(
					node.getOperations());
			for (POperation e : copy) {
				e.apply(this);
			}
		}

		sb.append("Next == ");

		Enumeration<String> e = this.c.getOperations().keys();
		while (e.hasMoreElements()) {
			String name = e.nextElement();

			sb.append(name);

			if (e.hasMoreElements()) {
				sb.append(" \\/ ");
			}
		}
		sb.append("\n");

	}

	@Override
	public void caseAOperation(AOperation node) {
		inAOperation(node);
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getReturnValues());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getOpName());
			for (TIdentifierLiteral e : copy) {
				sb.append(e.getText());
				e.apply(this);
			}
		}
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		sb.append(" == ");
		if (node.getOperationBody() != null) {
			node.getOperationBody().apply(this);
		}

		sb.append("\n");
		outAOperation(node);
	}

	/** Expression **/

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		inAIdentifierExpression(node);

		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());
			for (TIdentifierLiteral e : copy) {

				sb.append(e.getText());
				// e.apply(this);
			}
		}
		outAIdentifierExpression(node);
	}

	@Override
	public void caseAEqualPredicate(AEqualPredicate node) {
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		sb.append(" = ");
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
	}

	@Override
	public void caseAConjunctPredicate(AConjunctPredicate node) {
		inAConjunctPredicate(node);
		node.getLeft().apply(this);
		sb.append(" /\\ ");
		node.getRight().apply(this);
		outAConjunctPredicate(node);
	}

	@Override
	public void caseADisjunctPredicate(ADisjunctPredicate node) {
		inADisjunctPredicate(node);
		node.getLeft().apply(this);
		sb.append(" \\/ ");
		node.getRight().apply(this);
		outADisjunctPredicate(node);
	}

	@Override
	public void caseAIntegerExpression(AIntegerExpression node) {
		inAIntegerExpression(node);
		if (node.getLiteral() != null) {
			sb.append(node.getLiteral().getText());
			// node.getLiteral().apply(this);
		}
		outAIntegerExpression(node);
	}

	@Override
	public void caseAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		if (node.getName() != null) {
			sb.append(node.getName().getText());
			node.getName().apply(this);
		}
		sb.append(" == ");

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		if (node.getRhs() != null) {
			node.getRhs().apply(this);
		}
		sb.append("\n");
	}

	@Override
	public void caseAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		if (node.getName() != null) {
			sb.append(node.getName().getText());
			node.getName().apply(this);
		}
		sb.append(" == ");
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		if (node.getRhs() != null) {
			node.getRhs().apply(this);
		}
		sb.append("\n");
	}

	@Override
	public void caseADefinitionPredicate(ADefinitionPredicate node) {
		inADefinitionPredicate(node);
		if (node.getDefLiteral() != null) {
			node.getDefLiteral().apply(this);
		}
		sb.append(node.getDefLiteral().getText());
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getParameters());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outADefinitionPredicate(node);
	}

}
