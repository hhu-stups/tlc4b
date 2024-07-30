package de.tlc4b.analysis.transformation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAssertionsMachineClause;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AMachineReferenceNoParams;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASeesMachineClause;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.PMachineReferenceNoParams;
import de.be4.classicalb.core.parser.node.PParseUnit;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.Utils;

public class SeesEliminator extends DepthFirstAdapter {

	private final Start main;
	private final Map<String, Start> parsedMachines;
	private final ArrayList<String> resolvedMachines;

	public static void eliminateSeesClauses(Start start, Map<String, Start> parsedMachines) {
		new SeesEliminator(start, parsedMachines, new ArrayList<>());
	}

	private void eliminateSeenMachinesRecursively(Start start, Map<String, Start> parsedMachines,
	                                              ArrayList<String> resolvedMachines) {
		new SeesEliminator(start, parsedMachines, resolvedMachines);
	}

	private SeesEliminator(Start start, Map<String, Start> parsedMachines, ArrayList<String> resolvedMachines) {
		this.main = start;
		this.parsedMachines = parsedMachines;
		this.resolvedMachines = resolvedMachines;
		MachineClauseSorter.sortMachineClauses(start);
		start.apply(this);
	}

	public void inASeesMachineClause(ASeesMachineClause node) {
		for (PMachineReferenceNoParams pExpression : node.getMachineNames()) {
			AMachineReferenceNoParams id = (AMachineReferenceNoParams) pExpression;
			String machineName = Utils.getTIdentifierListAsString(id.getMachineName());
			if (!resolvedMachines.contains(machineName)) {
				resolvedMachines.add(machineName);
				Start start = parsedMachines.get(machineName);
				DefinitionsEliminator.eliminateDefinitions(start);
				eliminateSeenMachinesRecursively(start, parsedMachines, resolvedMachines);
				new MachineClauseAdder(main, start);
				if (node.parent() != null) {
					node.replaceBy(null);
				}
			}
		}
	}

	static class MachineClauseAdder extends DepthFirstAdapter {
		private final HashMap<Class<? extends PMachineClause>, PMachineClause> machineClauseHashMap;
		private final LinkedList<PMachineClause> additionalMachineClauseList;

		public MachineClauseAdder(Start main, Start seenMachineStart) {
			ArrayList<PMachineClause> machineClausesList = new ArrayList<>();
			this.machineClauseHashMap = new LinkedHashMap<>();
			this.additionalMachineClauseList = new LinkedList<>();

			PParseUnit pParseUnit = main.getPParseUnit();
			AAbstractMachineParseUnit machineParseUnit = (AAbstractMachineParseUnit) pParseUnit;

			for (PMachineClause machineClause : machineParseUnit.getMachineClauses()) {
				machineClausesList.add(machineClause);
				machineClauseHashMap.put(machineClause.getClass(), machineClause);
			}

			seenMachineStart.apply(this);

			LinkedList<PMachineClause> newMachineClauseList = new LinkedList<>();
			for (PMachineClause pMachineClause : machineClausesList) {
				pMachineClause.replaceBy(null); // delete parent of clause
				newMachineClauseList.add(pMachineClause);
			}
			newMachineClauseList.addAll(additionalMachineClauseList);
			machineParseUnit.setMachineClauses(newMachineClauseList);
		}

		@Override
		public void caseAConstantsMachineClause(AConstantsMachineClause node) {
			AConstantsMachineClause main = (AConstantsMachineClause) machineClauseHashMap.get(node.getClass());

			if (main == null) {
				additionalMachineClauseList.add(node);
			} else {
				ArrayList<PExpression> oldConstantsList = new ArrayList<>(main.getIdentifiers());
				ArrayList<PExpression> newConstantsList = new ArrayList<>();
				for (PExpression pExpression : oldConstantsList) {
					pExpression.replaceBy(null); // delete parent
					newConstantsList.add(pExpression);
				}
				ArrayList<PExpression> otherConstants = new ArrayList<>(node.getIdentifiers());

				for (PExpression pExpression : otherConstants) {
					pExpression.replaceBy(null); // delete parent
					newConstantsList.add(pExpression);
				}
				main.setIdentifiers(newConstantsList);
			}
		}

		public void caseAAbstractConstantsMachineClause(AAbstractConstantsMachineClause node) {
			AAbstractConstantsMachineClause main = (AAbstractConstantsMachineClause) machineClauseHashMap.get(node.getClass());

			if (main != null) {
				ArrayList<PExpression> oldConstantsList = new ArrayList<>(main.getIdentifiers());
				ArrayList<PExpression> newConstantsList = new ArrayList<>();
				for (PExpression pExpression : oldConstantsList) {
					pExpression.replaceBy(null); // delete parent
					newConstantsList.add(pExpression);
				}
				ArrayList<PExpression> otherConstants = new ArrayList<>(node.getIdentifiers());

				for (PExpression pExpression : otherConstants) {
					pExpression.replaceBy(null); // delete parent
					newConstantsList.add(pExpression);

				}
				main.setIdentifiers(newConstantsList);
			} else {
				additionalMachineClauseList.add(node);
			}

		}

		@Override
		public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
			APropertiesMachineClause main = (APropertiesMachineClause) machineClauseHashMap.get(node.getClass());
			if (main == null) {
				additionalMachineClauseList.add(node);
			} else {
				AConjunctPredicate con = new AConjunctPredicate();
				con.setLeft(main.getPredicates());
				con.setRight(node.getPredicates());
				main.setPredicates(con);
			}

		}

		@Override
		public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
			ADefinitionsMachineClause main = (ADefinitionsMachineClause) machineClauseHashMap.get(node.getClass());

			if (main == null) {
				additionalMachineClauseList.add(node);
			} else {
				ArrayList<PDefinition> oldDefinitions = new ArrayList<>(main.getDefinitions());
				ArrayList<PDefinition> newDefinitionsList = new ArrayList<>();
				for (PDefinition pExpression : oldDefinitions) {
					pExpression.replaceBy(null); // delete parent
					newDefinitionsList.add(pExpression);
				}
				ArrayList<PDefinition> otherConstants = new ArrayList<>(node.getDefinitions());

				for (PDefinition definition : otherConstants) {
					if (definition.parent() != null) {
						definition.replaceBy(null); // delete parent
					}
					newDefinitionsList.add(definition);

				}
				main.setDefinitions(newDefinitionsList);
			}
		}

		public void caseAAssertionsMachineClause(AAssertionsMachineClause node) {
			AAssertionsMachineClause main = (AAssertionsMachineClause) machineClauseHashMap.get(node.getClass());
			if (main == null) {
				additionalMachineClauseList.add(node);
			} else {
				ArrayList<PPredicate> old = new ArrayList<>(main.getPredicates());
				ArrayList<PPredicate> newList = new ArrayList<>();
				for (PPredicate p : old) {
					p.replaceBy(null); // delete parent
					newList.add(p);
				}
				ArrayList<PPredicate> otherAssertions = new ArrayList<>(node.getPredicates());

				for (PPredicate p : otherAssertions) {
					if (p.parent() != null) {
						p.replaceBy(null); // delete parent
					}
					newList.add(p);

				}
				main.setPredicates(newList);
			}
		}
	}
}
