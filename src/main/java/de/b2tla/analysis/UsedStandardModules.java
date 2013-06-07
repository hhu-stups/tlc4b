package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.Collections;

import de.b2tla.analysis.nodes.NodeType;
import de.b2tla.btypes.BType;
import de.b2tla.btypes.FunctionType;
import de.b2tla.btypes.IntegerType;
import de.b2tla.btypes.SetType;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AClosureExpression;
import de.be4.classicalb.core.parser.node.ACompositionExpression;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConcatExpression;
import de.be4.classicalb.core.parser.node.ADirectProductExpression;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.ADomainRestrictionExpression;
import de.be4.classicalb.core.parser.node.ADomainSubtractionExpression;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AFin1SubsetExpression;
import de.be4.classicalb.core.parser.node.AFinSubsetExpression;
import de.be4.classicalb.core.parser.node.AFirstExpression;
import de.be4.classicalb.core.parser.node.AFirstProjectionExpression;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AFrontExpression;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AGeneralConcatExpression;
import de.be4.classicalb.core.parser.node.AGeneralIntersectionExpression;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AGeneralUnionExpression;
import de.be4.classicalb.core.parser.node.AGreaterEqualPredicate;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentityExpression;
import de.be4.classicalb.core.parser.node.AImageExpression;
import de.be4.classicalb.core.parser.node.AInsertFrontExpression;
import de.be4.classicalb.core.parser.node.AIntSetExpression;
import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.AIseq1Expression;
import de.be4.classicalb.core.parser.node.AIseqExpression;
import de.be4.classicalb.core.parser.node.AIterationExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALastExpression;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.ALessPredicate;
import de.be4.classicalb.core.parser.node.AMaxExpression;
import de.be4.classicalb.core.parser.node.AMinExpression;
import de.be4.classicalb.core.parser.node.AMinusExpression;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AModuloExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.ANat1SetExpression;
import de.be4.classicalb.core.parser.node.ANatSetExpression;
import de.be4.classicalb.core.parser.node.ANatural1SetExpression;
import de.be4.classicalb.core.parser.node.ANaturalSetExpression;
import de.be4.classicalb.core.parser.node.ANotSubsetPredicate;
import de.be4.classicalb.core.parser.node.ANotSubsetStrictPredicate;
import de.be4.classicalb.core.parser.node.AOverwriteExpression;
import de.be4.classicalb.core.parser.node.AParallelProductExpression;
import de.be4.classicalb.core.parser.node.APartialBijectionExpression;
import de.be4.classicalb.core.parser.node.APartialFunctionExpression;
import de.be4.classicalb.core.parser.node.APartialInjectionExpression;
import de.be4.classicalb.core.parser.node.APartialSurjectionExpression;
import de.be4.classicalb.core.parser.node.APermExpression;
import de.be4.classicalb.core.parser.node.APow1SubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APredecessorExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ARangeExpression;
import de.be4.classicalb.core.parser.node.ARangeRestrictionExpression;
import de.be4.classicalb.core.parser.node.ARangeSubtractionExpression;
import de.be4.classicalb.core.parser.node.AReflexiveClosureExpression;
import de.be4.classicalb.core.parser.node.ARelationsExpression;
import de.be4.classicalb.core.parser.node.ARestrictFrontExpression;
import de.be4.classicalb.core.parser.node.ARestrictTailExpression;
import de.be4.classicalb.core.parser.node.ARevExpression;
import de.be4.classicalb.core.parser.node.AReverseExpression;
import de.be4.classicalb.core.parser.node.ASecondProjectionExpression;
import de.be4.classicalb.core.parser.node.ASeq1Expression;
import de.be4.classicalb.core.parser.node.ASeqExpression;
import de.be4.classicalb.core.parser.node.ASizeExpression;
import de.be4.classicalb.core.parser.node.ASubsetStrictPredicate;
import de.be4.classicalb.core.parser.node.ASuccessorExpression;
import de.be4.classicalb.core.parser.node.ATailExpression;
import de.be4.classicalb.core.parser.node.ATotalBijectionExpression;
import de.be4.classicalb.core.parser.node.ATotalFunctionExpression;
import de.be4.classicalb.core.parser.node.ATotalInjectionExpression;
import de.be4.classicalb.core.parser.node.ATotalSurjectionExpression;
import de.be4.classicalb.core.parser.node.ATransFunctionExpression;
import de.be4.classicalb.core.parser.node.ATransRelationExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;

public class UsedStandardModules extends DepthFirstAdapter {

	public static enum STANDARD_MODULES {
		Naturals, Integers, FiniteSets, Sequences, TLC, BBuiltIns, Relations, FunctionsAsRelations, Functions, SequencesExtended, SequencesAsRelations
	}

	private final static ArrayList<STANDARD_MODULES> modules = new ArrayList<UsedStandardModules.STANDARD_MODULES>();
	static {
		modules.add(STANDARD_MODULES.Naturals);
		modules.add(STANDARD_MODULES.Integers);
		modules.add(STANDARD_MODULES.FiniteSets);
		modules.add(STANDARD_MODULES.Sequences);
		modules.add(STANDARD_MODULES.TLC);
		modules.add(STANDARD_MODULES.BBuiltIns);
		modules.add(STANDARD_MODULES.Relations);
		modules.add(STANDARD_MODULES.Functions);
		modules.add(STANDARD_MODULES.FunctionsAsRelations);
		modules.add(STANDARD_MODULES.SequencesExtended);
		modules.add(STANDARD_MODULES.SequencesAsRelations);
	}

	private Set<STANDARD_MODULES> usedStandardModules;
	private Typechecker typechecker;
	private Hashtable<Node, NodeType> restrictedTypesTable;

	public UsedStandardModules(Typechecker typechecker,
			Hashtable<Node, NodeType> restrictedTypesTable) {
		this.usedStandardModules = new HashSet<STANDARD_MODULES>();
		this.typechecker = typechecker;
		this.restrictedTypesTable = restrictedTypesTable;
	}

	class StandardModuleComparator implements Comparator<STANDARD_MODULES> {
		public int compare(STANDARD_MODULES s1, STANDARD_MODULES s2) {
			Integer i1 = new Integer(modules.indexOf(s1));
			Integer i2 = new Integer(modules.indexOf(s2));
			return i1.compareTo(i2);
		}

	}

	public ArrayList<STANDARD_MODULES> getUsedModules() {
		ArrayList<STANDARD_MODULES> list = new ArrayList<STANDARD_MODULES>(
				usedStandardModules);
		if (list.contains(STANDARD_MODULES.Integers)) {
			list.remove(STANDARD_MODULES.Naturals);
		}
		Collections.sort(list, new StandardModuleComparator());
		return list;
	}

	private void containsStandardModule(Node node) {
		if (restrictedTypesTable.containsKey(node)) {
			return;
		}
		// TODO add types beside Integer
		BType t = typechecker.getType(node);

		if (t instanceof IntegerType) {

			usedStandardModules.add(STANDARD_MODULES.Integers);
		}
	}

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		inALambdaExpression(node);
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				containsStandardModule(e);
				e.apply(this);
			}
		}
		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		outALambdaExpression(node);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		inAComprehensionSetExpression(node);
		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			for (PExpression e : copy) {
				containsStandardModule(e);
				e.apply(this);
			}
		}
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		outAComprehensionSetExpression(node);
	}

	/**
	 * Bounded Variables
	 * 
	 */
	public void inAForallPredicate(AForallPredicate node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			NodeType n = restrictedTypesTable.get(e);
			if (n != null)
				continue;
			BType t = typechecker.getType(e);
			if (t.containsIntegerType()) {
				usedStandardModules.add(STANDARD_MODULES.Integers);
			}
		}
		node.getImplication().apply(this);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			NodeType n = restrictedTypesTable.get(e);
			if (n != null)
				continue;
			BType t = typechecker.getType(e);
			if (t.containsIntegerType()) {
				usedStandardModules.add(STANDARD_MODULES.Integers);
			}
		}
		node.getPredicate().apply(this);
	}

	/**
	 * Naturals
	 */

	@Override
	public void caseANaturalSetExpression(ANaturalSetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	@Override
	public void caseANatural1SetExpression(ANatural1SetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	@Override
	public void caseANatSetExpression(ANatSetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	@Override
	public void caseANat1SetExpression(ANat1SetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inALessEqualPredicate(ALessEqualPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inALessPredicate(ALessPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAGreaterEqualPredicate(AGreaterEqualPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAGreaterPredicate(AGreaterPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAAddExpression(AAddExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAMinusExpression(AMinusExpression node) {
		// TODO what is a AMinusExpression
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAIntervalExpression(AIntervalExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAMinExpression(AMinExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAMaxExpression(AMaxExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inADivExpression(ADivExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAPowerOfExpression(APowerOfExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAModuloExpression(AModuloExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Naturals);
	}

	public void inAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		BType t = typechecker.getType(node);
		if (t instanceof IntegerType) {
			usedStandardModules.add(STANDARD_MODULES.Naturals);
		}
	}

	public void inAMultOrCartExpression(AMultOrCartExpression node) {
		BType t = typechecker.getType(node);
		if (t instanceof IntegerType) {
			usedStandardModules.add(STANDARD_MODULES.Naturals);
		} else {
			// usedStandardModules.add(STANDARD_MODULES.RelationsNew);
		}
	}

	/**
	 * Integers
	 */

	public void inAIntSetExpression(AIntSetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Integers);
	}

	public void inAIntegerSetExpression(AIntegerSetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Integers);
	}

	public void inAUnaryMinusExpression(AUnaryMinusExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Integers);
	}

	/**
	 * FiniteSets
	 */
	public void inACardExpression(ACardExpression node) {
		usedStandardModules.add(STANDARD_MODULES.FiniteSets);
	}

	/**
	 * BBuiltIns
	 */
	public void inAGeneralSumExpression(AGeneralSumExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAGeneralProductExpression(AGeneralProductExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inASuccessorExpression(ASuccessorExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAPredecessorExpression(APredecessorExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAPow1SubsetExpression(APow1SubsetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAFinSubsetExpression(AFinSubsetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAFin1SubsetExpression(AFin1SubsetExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inANotSubsetPredicate(ANotSubsetPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inANotSubsetStrictPredicate(ANotSubsetStrictPredicate node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAGeneralIntersectionExpression(
			AGeneralIntersectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAGeneralUnionExpression(AGeneralUnionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	/**
	 * Functions
	 */

	public void inARangeExpression(ARangeExpression node) {
		BType type = typechecker.getType(node.getExpression());
		if (type instanceof FunctionType) {
			usedStandardModules.add(STANDARD_MODULES.Functions);
		} else {
			usedStandardModules.add(STANDARD_MODULES.Relations);
		}
	}

	public void inAImageExpression(AImageExpression node) {
		BType type = typechecker.getType(node.getLeft());
		if (type instanceof FunctionType) {
			usedStandardModules.add(STANDARD_MODULES.Functions);
		} else {
			usedStandardModules.add(STANDARD_MODULES.Relations);
		}
	}

	private void setOfFunctions(Node node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof FunctionType) {
			usedStandardModules.add(STANDARD_MODULES.Functions);
		} else {
			usedStandardModules.add(STANDARD_MODULES.FunctionsAsRelations);
		}
	}

	public void inAPartialFunctionExpression(APartialFunctionExpression node) {
		setOfFunctions(node);
	}

	public void inATotalInjectionExpression(ATotalInjectionExpression node) {
		setOfFunctions(node);
	}

	public void inAPartialInjectionExpression(APartialInjectionExpression node) {
		setOfFunctions(node);
	}

	public void inATotalSurjectionExpression(ATotalSurjectionExpression node) {
		setOfFunctions(node);
	}

	public void inAPartialSurjectionExpression(APartialSurjectionExpression node) {
		setOfFunctions(node);
	}

	public void inATotalBijectionExpression(ATotalBijectionExpression node) {
		setOfFunctions(node);
	}

	public void inAPartialBijectionExpression(APartialBijectionExpression node) {
		setOfFunctions(node);
	}

	/**
	 * Functions as Relations
	 */

	// Function call
	public void inAFunctionExpression(AFunctionExpression node) {
		BType type = typechecker.getType(node.getIdentifier());
		if (type instanceof SetType) {
			usedStandardModules.add(STANDARD_MODULES.FunctionsAsRelations);
		}
	}

	public void inATotalFunctionExpression(ATotalFunctionExpression node) {
		SetType type = (SetType) typechecker.getType(node);
		if (type.getSubtype() instanceof SetType) {
			usedStandardModules.add(STANDARD_MODULES.FunctionsAsRelations);
		}
	}

	/**
	 * Relations
	 */
	public void inARelationsExpression(ARelationsExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inADomainExpression(ADomainExpression node) {
		BType t = typechecker.getType(node.getExpression());
		if (!(t instanceof FunctionType)) {
			usedStandardModules.add(STANDARD_MODULES.Relations);
		}
	}

	public void inAIdentityExpression(AIdentityExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inADomainRestrictionExpression(ADomainRestrictionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inADomainSubtractionExpression(ADomainSubtractionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inARangeRestrictionExpression(ARangeRestrictionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inARangeSubtractionExpression(ARangeSubtractionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAReverseExpression(AReverseExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAOverwriteExpression(AOverwriteExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(node.getLhsExpression());
        for(PExpression e : copy)
        {
        	if (e instanceof AFunctionExpression) {
        		usedStandardModules.add(STANDARD_MODULES.Relations);
        	}
        }
	}

	public void inADirectProductExpression(ADirectProductExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAParallelProductExpression(AParallelProductExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inACompositionExpression(ACompositionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAFirstProjectionExpression(AFirstProjectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inASecondProjectionExpression(ASecondProjectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAIterationExpression(AIterationExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAClosureExpression(AClosureExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAReflexiveClosureExpression(AReflexiveClosureExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inATransFunctionExpression(ATransFunctionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inATransRelationExpression(ATransRelationExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	/**
	 * Sequences
	 */

	public void inASeqExpression(ASeqExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Sequences);
	}

	public void inASizeExpression(ASizeExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Sequences);
	}

	public void inAConcatExpression(AConcatExpression node) {
		evalSequenceOrRelation(node);
	}

	private void evalSequenceOrRelation(Node node) {
		BType type = typechecker.getType(node);
		if (type instanceof FunctionType) {
			usedStandardModules.add(STANDARD_MODULES.Sequences);
		} else {
			usedStandardModules.add(STANDARD_MODULES.SequencesAsRelations);
		}
	}

	public void inAFirstExpression(AFirstExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Sequences);
	}

	public void inATailExpression(ATailExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Sequences);
	}

	/**
	 * SequencesExtended
	 */

	public void inAIseqExpression(AIseqExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inASeq1Expression(ASeq1Expression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inAInsertFrontExpression(AInsertFrontExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inALastExpression(ALastExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inAFrontExpression(AFrontExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inAPermExpression(APermExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inARevExpression(ARevExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inAGeneralConcatExpression(AGeneralConcatExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inARestrictFrontExpression(ARestrictFrontExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	public void inARestrictTailExpression(ARestrictTailExpression node) {
		usedStandardModules.add(STANDARD_MODULES.SequencesExtended);
	}

	/**
	 * sonst
	 * 
	 */

	public void inAIseq1Expression(AIseq1Expression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

}
