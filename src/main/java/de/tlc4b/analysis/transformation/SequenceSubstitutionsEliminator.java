package de.tlc4b.analysis.transformation;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;

import java.util.*;
import java.util.stream.Collectors;

import static de.tlc4b.MP.println;

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
	private boolean initialisationMode = false, replacementMode = false;
	private final Set<List<String>> assignedVariables = new HashSet<>();
	private final Set<List<String>> parallelAssignedVariables = new HashSet<>();
	private final Deque<Set<List<String>>> currentAssignedVariables = new ArrayDeque<>();
	private final Set<Node> primeNodes = new HashSet<>();
	private final Deque<SubstitutionMode> modeStack = new ArrayDeque<>();

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
			}
			// TODO: what to do with AFunctionExpression?
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

		if (!initialisationMode && replacementMode && !currentAssignedVariables.isEmpty()
				&& currentAssignedVariables.getFirst().contains(identifierToStringList(node))) {
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

		Set<List<String>> variables = new HashSet<>();
		if (!currentAssignedVariables.isEmpty()) {
			variables.addAll(currentAssignedVariables.getFirst());
		}
		currentAssignedVariables.push(variables);
	}

	@Override
	public void outAParallelSubstitution(AParallelSubstitution node) {
		if (modeStack.removeFirst() != SubstitutionMode.PARALLEL) {
			throw new IllegalStateException("expected PARALLEL mode");
		}

		parallelAssignedVariables.addAll(currentAssignedVariables.removeFirst());
		if (!modeStack.isEmpty() && modeStack.getFirst() == SubstitutionMode.SEQUENTIAL) {
			currentAssignedVariables.getFirst().addAll(parallelAssignedVariables);
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

		Set<List<String>> variables = new HashSet<>();
		if (!currentAssignedVariables.isEmpty()) {
			variables.addAll(currentAssignedVariables.getFirst());
		}
		currentAssignedVariables.push(variables);
	}

	@Override
	public void outASequenceSubstitution(ASequenceSubstitution node) {
		node.replaceBy(new AParallelSubstitution(new ArrayList<>(node.getSubstitutions())));
		println(node.getStartPos() + "-" + node.getEndPos() + ": replaced sequential substitution by parallel substitution");

		if (modeStack.removeFirst() != SubstitutionMode.SEQUENTIAL) {
			throw new IllegalStateException("expected SEQUENTIAL mode");
		}

		Set<List<String>> currVariables = currentAssignedVariables.removeFirst();
		if (!modeStack.isEmpty() && modeStack.getFirst() == SubstitutionMode.PARALLEL) {
			parallelAssignedVariables.addAll(currVariables);
		} else if (!currentAssignedVariables.isEmpty()) {
			currentAssignedVariables.getFirst().addAll(currVariables);
		}

		if (topLevel.equals(node)) {
			topLevel = null;
			parallelAssignedVariables.clear();
			currentAssignedVariables.clear();
		}
	}

	private void assignVariables(AIdentifierExpression lhs) {
		if (modeStack.getFirst().equals(SubstitutionMode.SEQUENTIAL) && !currentAssignedVariables.isEmpty()) {
			currentAssignedVariables.getFirst().add(identifierToStringList(lhs));
		} else if (modeStack.getFirst().equals(SubstitutionMode.PARALLEL)) {
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
