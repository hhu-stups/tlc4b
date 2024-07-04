package de.tlc4b.analysis.transformation;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Replace all SequenceSubstitutions by ParallelSubstitutions.
 * Whether the assignments are still valid is checked later by the AssignedVariablesFinder
 * and UnchangedVariablesFinder, which are called by the Translator.
 */
public class SequenceSubstitutionsEliminator extends DepthFirstAdapter {

	public static void eliminateSequenceSubstitutions(Start start) {
		new SequenceSubstitutionsEliminator(start);
	}

	private SequenceSubstitutionsEliminator(Start start) {
		start.apply(this);
	}

	@Override
	public void caseASequenceSubstitution(ASequenceSubstitution node) {
		node.replaceBy(new AParallelSubstitution(new ArrayList<>(node.getSubstitutions())));
	}
}
