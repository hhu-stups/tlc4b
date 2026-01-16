package de.tlc4b.analysis.transformation;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.AConcreteVariablesMachineClause;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASeesMachineClause;
import de.be4.classicalb.core.parser.node.ASetsMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Start;

/**
 * Sort the machine clauses:
 * 	1. import clauses
 * 	2. declaration clauses
 * 	3. properties clauses
 * 	4. operation clauses
 */
public class MachineClauseSorter extends DepthFirstAdapter {

	private static final Map<Object, Integer> PRIORITY = new HashMap<>();
	static {
		// declarations clauses
		// TODO: can we add?: PRIORITY.put(AUsesMachineClause.class, 0);
		PRIORITY.put(ASeesMachineClause.class, 1);
		PRIORITY.put(ASetsMachineClause.class, 2);
		PRIORITY.put(AAbstractConstantsMachineClause.class, 3);
		PRIORITY.put(AConstantsMachineClause.class, 4);
		PRIORITY.put(AVariablesMachineClause.class, 5);
		PRIORITY.put(AConcreteVariablesMachineClause.class, 6);
		PRIORITY.put(ADefinitionsMachineClause.class, 7);

		// properties clauses
		PRIORITY.put(AConstraintsMachineClause.class, 8);
		PRIORITY.put(APropertiesMachineClause.class, 9);
		PRIORITY.put(AInvariantMachineClause.class, 10);
		PRIORITY.put(AAssertionsMachineClause.class, 11);
		PRIORITY.put(AOperationsMachineClause.class, 12);
		PRIORITY.put(AInitialisationMachineClause.class, 13);
	}

	public static void sortMachineClauses(Start start) {
		start.apply(new MachineClauseSorter());
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		node.getMachineClauses().sort(Comparator.comparing(arg -> PRIORITY.get(arg.getClass())));
	}
}
