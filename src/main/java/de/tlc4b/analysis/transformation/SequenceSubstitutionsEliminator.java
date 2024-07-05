package de.tlc4b.analysis.transformation;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Replace all SequenceSubstitutions by ParallelSubstitutions.
 * Whether the assignments are still valid is checked later by the AssignedVariablesFinder
 * and UnchangedVariablesFinder, which are called by the Translator.
 */
public class SequenceSubstitutionsEliminator extends DepthFirstAdapter {

	private ASequenceSubstitution topLevel = null;
	private boolean initialisationMode = false, replacementMode = false;
	private final Set<List<String>> assignments = new HashSet<>();
	private final Set<Node> primeNodes = new HashSet<>();

	public SequenceSubstitutionsEliminator(Start start) {
		start.apply(this);
	}

	@Override
	public void inAAssignSubstitution(AAssignSubstitution node) {
		if (topLevel == null)
			return;

		for (PExpression lhs : node.getLhsExpression()) {
			if (lhs instanceof AIdentifierExpression) {
				assignments.add(identifierToStringList((AIdentifierExpression) lhs));
			}
			// TODO: what to do with AFunctionExpression?
		}
	}

	@Override
	public void outAAssignSubstitution(AAssignSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		for (PExpression rhs : node.getRhsExpressions()) {
			rhs.apply(this);
		}
		replacementMode = false;
	}

	@Override
	public void inABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		if (topLevel == null)
			return;

		for (PExpression lhs : node.getIdentifiers()) {
			if (lhs instanceof AIdentifierExpression) {
				assignments.add(identifierToStringList((AIdentifierExpression) lhs));
			}
		}
	}

	@Override
	public void outABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getSet().apply(this);
		replacementMode = false;
	}

	@Override
	public void inABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		if (topLevel == null)
			return;

		for (PExpression lhs : node.getIdentifiers()) {
			if (lhs instanceof AIdentifierExpression) {
				assignments.add(identifierToStringList((AIdentifierExpression) lhs));
			}
		}
	}

	@Override
	public void outABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getPredicate().apply(this);
		replacementMode = false;
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (topLevel == null)
			return;

		System.out.println(node);
		if (!initialisationMode && replacementMode && assignments.contains(identifierToStringList(node))) {
			System.out.println("SUCC" + node);
			primeNodes.add(node);
		}
	}

	@Override
	public void inAInitialisationMachineClause(AInitialisationMachineClause node) {
		initialisationMode = true;
	}

	@Override
	public void outAInitialisationMachineClause(AInitialisationMachineClause node) {
		initialisationMode = false;
	}

	@Override
	public void inASequenceSubstitution(ASequenceSubstitution node) {
		if (topLevel == null) {
			topLevel = node;
		}
	}

	@Override
	public void outASequenceSubstitution(ASequenceSubstitution node) {
		if (topLevel.equals(node)) {
			topLevel = null;
			assignments.clear();
		}
		node.replaceBy(new AParallelSubstitution(new ArrayList<>(node.getSubstitutions())));
	}

	private static List<String> identifierToStringList(AIdentifierExpression identifier) {
		return identifier.getIdentifier().stream().map(Token::getText).collect(Collectors.toList());
	}

	public Set<Node> getPrimeNodes() {
		return primeNodes;
	}
}
