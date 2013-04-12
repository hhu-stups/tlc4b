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
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConcatExpression;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.ADomainRestrictionExpression;
import de.be4.classicalb.core.parser.node.ADomainSubtractionExpression;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AFin1SubsetExpression;
import de.be4.classicalb.core.parser.node.AFinSubsetExpression;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AGeneralIntersectionExpression;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
import de.be4.classicalb.core.parser.node.AGreaterEqualPredicate;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentityExpression;
import de.be4.classicalb.core.parser.node.AImageExpression;
import de.be4.classicalb.core.parser.node.AIntSetExpression;
import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.AIseq1Expression;
import de.be4.classicalb.core.parser.node.AIseqExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
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
import de.be4.classicalb.core.parser.node.APartialFunctionExpression;
import de.be4.classicalb.core.parser.node.APartialInjectionExpression;
import de.be4.classicalb.core.parser.node.APow1SubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APredecessorExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedIntersectionExpression;
import de.be4.classicalb.core.parser.node.AQuantifiedUnionExpression;
import de.be4.classicalb.core.parser.node.ARangeExpression;
import de.be4.classicalb.core.parser.node.ARelationsExpression;
import de.be4.classicalb.core.parser.node.AReverseExpression;
import de.be4.classicalb.core.parser.node.ASubsetStrictPredicate;
import de.be4.classicalb.core.parser.node.ASuccessorExpression;
import de.be4.classicalb.core.parser.node.ATotalFunctionExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;

public class UsedStandardModules extends DepthFirstAdapter {

	public static enum STANDARD_MODULES {
		Naturals, Integers, FiniteSets, Sequences, TLC, BBuiltIns, Relations

	}

	public final static ArrayList<STANDARD_MODULES> modules = new ArrayList<UsedStandardModules.STANDARD_MODULES>();
	static {
		modules.add(STANDARD_MODULES.Naturals);
		modules.add(STANDARD_MODULES.Integers);
		modules.add(STANDARD_MODULES.FiniteSets);
		modules.add(STANDARD_MODULES.Sequences);
		modules.add(STANDARD_MODULES.TLC);
		modules.add(STANDARD_MODULES.BBuiltIns);
		modules.add(STANDARD_MODULES.Relations);
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
			// usedStandardModules.add(STANDARD_MODULES.Relations);
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

	public void inASubsetStrictPredicate(ASubsetStrictPredicate node) {
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

	public void inAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
	}

	public void inAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.BBuiltIns);
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

	public void inARangeExpression(ARangeExpression node) {
			usedStandardModules.add(STANDARD_MODULES.Relations);
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

	public void inAPartialFunctionExpression(APartialFunctionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAReverseExpression(AReverseExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAImageExpression(AImageExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAPartialInjectionExpression(APartialInjectionExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAOverwriteExpression(AOverwriteExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAIseqExpression(AIseqExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAIseq1Expression(AIseq1Expression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inAConcatExpression(AConcatExpression node) {
		usedStandardModules.add(STANDARD_MODULES.Relations);
	}

	public void inATotalFunctionExpression(ATotalFunctionExpression node) {
		SetType type = (SetType) typechecker.getType(node);
		if (type.getSubtype() instanceof SetType) {
			usedStandardModules.add(STANDARD_MODULES.Relations);
		}
	}

	public void inAFunctionExpression(AFunctionExpression node) {
		BType type = typechecker.getType(node);
		if (type instanceof SetType) {
			usedStandardModules.add(STANDARD_MODULES.Relations);
		}
	}
}
