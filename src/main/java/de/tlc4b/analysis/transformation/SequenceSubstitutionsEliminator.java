package de.tlc4b.analysis.transformation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;
import de.tlc4b.MP;
import de.tlc4b.exceptions.NotSupportedException;

/**
 * Replace all SequenceSubstitutions by ParallelSubstitutions.
 * Replace sequentially assigned identifiers by primed identifiers,
 * e.g. x := 1 ; y := x will be translated to x' = 1 /\ y' = x'.
 * Whether the assignments are still valid is checked later by the AssignedVariablesFinder
 * and UnchangedVariablesFinder, which are called by the Translator.
 */
public class SequenceSubstitutionsEliminator extends DepthFirstAdapter {

	private enum SubstitutionMode {
		PARALLEL,
		SEQUENTIAL
	}

	private ASequenceSubstitution topLevel = null;
	private boolean initialisationMode = false;
	private boolean replacementMode = false;

	private final Set<List<String>> parallelAssignedVariables = new HashSet<>();
	private final Set<List<String>> currentAssignedVariables = new HashSet<>();
	private final Deque<SubstitutionMode> modeStack = new ArrayDeque<>();
	private final Set<Node> primeNodes = new HashSet<>();

	public SequenceSubstitutionsEliminator(Start start) {
		start.apply(this);
	}

	@Override
	public void inAAnySubstitution(AAnySubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getWhere().apply(this);
		replacementMode = false;
	}

	@Override
	public void inAAssertionSubstitution(AAssertionSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getPredicate().apply(this);
		replacementMode = false;
	}

	@Override
	public void inAAssignSubstitution(AAssignSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		for (PExpression rhs : node.getRhsExpressions()) {
			rhs.apply(this);
		}
		replacementMode = false;

		for (PExpression lhs : node.getLhsExpression()) {
			if (lhs instanceof AIdentifierExpression) {
				assignVariables((AIdentifierExpression) lhs);
			} else if (lhs instanceof AFunctionExpression) {
				// TODO: what to do with AFunctionExpression?
				throw new NotSupportedException("function assignments in sequential substitutions are not yet supported");
			}
		}
	}

	@Override
	public void inABecomesElementOfSubstitution(ABecomesElementOfSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getSet().apply(this);
		replacementMode = false;

		for (PExpression lhs : node.getIdentifiers()) {
			if (lhs instanceof AIdentifierExpression) {
				assignVariables((AIdentifierExpression) lhs);
			}
		}
	}

	@Override
	public void inABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getPredicate().apply(this);
		replacementMode = false;

		for (PExpression lhs : node.getIdentifiers()) {
			if (lhs instanceof AIdentifierExpression) {
				assignVariables((AIdentifierExpression) lhs);
			}
		}
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		if (topLevel == null)
			return;

		// mark identifiers that have already been assigned in the current block as primed
		if (!initialisationMode && replacementMode && currentAssignedVariables.contains(identifierToStringList(node))) {
			primeNodes.add(node);
		}
	}

	@Override
	public void inAIfSubstitution(AIfSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getCondition().apply(this);
		replacementMode = false;
	}

	@Override
	public void inAIfElsifSubstitution(AIfElsifSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getCondition().apply(this);
		replacementMode = false;
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
	public void inALetSubstitution(ALetSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getPredicate().apply(this);
		replacementMode = false;
	}

	@Override
	public void inAParallelSubstitution(AParallelSubstitution node) {
		modeStack.push(SubstitutionMode.PARALLEL);
	}

	@Override
	public void outAParallelSubstitution(AParallelSubstitution node) {
		if (modeStack.removeFirst() != SubstitutionMode.PARALLEL) {
			throw new IllegalStateException("expected PARALLEL mode");
		}

		if (modeStack.peekFirst() == SubstitutionMode.SEQUENTIAL) {
			currentAssignedVariables.addAll(parallelAssignedVariables);
			parallelAssignedVariables.clear();
		}
	}

	@Override
	public void inAPreconditionSubstitution(APreconditionSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getPredicate().apply(this);
		replacementMode = false;
	}

	@Override
	public void inASelectSubstitution(ASelectSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getCondition().apply(this);
		replacementMode = false;
	}

	@Override
	public void inASelectWhenSubstitution(ASelectWhenSubstitution node) {
		if (topLevel == null)
			return;

		replacementMode = true;
		node.getCondition().apply(this);
		replacementMode = false;
	}

	@Override
	public void inASequenceSubstitution(ASequenceSubstitution node) {
		if (topLevel == null) {
			topLevel = node;
		}
		modeStack.push(SubstitutionMode.SEQUENTIAL);
	}

	@Override
	public void outASequenceSubstitution(ASequenceSubstitution node) {
		node.replaceBy(new AParallelSubstitution(new ArrayList<>(node.getSubstitutions())));
		MP.printlnVerbose(node.getStartPos() + "-" + node.getEndPos() + ": replaced sequential substitution by parallel substitution");

		if (modeStack.pollFirst() != SubstitutionMode.SEQUENTIAL) {
			throw new IllegalStateException("expected SEQUENTIAL mode");
		}

		if (topLevel.equals(node)) {
			topLevel = null;
			parallelAssignedVariables.clear();
			currentAssignedVariables.clear();
		}
	}

	private void assignVariables(AIdentifierExpression lhs) {
		if (modeStack.peekFirst() == SubstitutionMode.SEQUENTIAL) {
			currentAssignedVariables.add(identifierToStringList(lhs));
		} else if (modeStack.peekFirst() == SubstitutionMode.PARALLEL) {
			parallelAssignedVariables.add(identifierToStringList(lhs));
		}
	}

	private static List<String> identifierToStringList(AIdentifierExpression identifier) {
		return identifier.getIdentifier().stream().map(Token::getText).collect(Collectors.toList());
	}

	public Set<Node> getPrimeNodes() {
		return primeNodes;
	}
}
