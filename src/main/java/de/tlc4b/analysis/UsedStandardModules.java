package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AClosureExpression;
import de.be4.classicalb.core.parser.node.ACompositionExpression;
import de.be4.classicalb.core.parser.node.AConcatExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADirectProductExpression;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.ADomainRestrictionExpression;
import de.be4.classicalb.core.parser.node.ADomainSubtractionExpression;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AFin1SubsetExpression;
import de.be4.classicalb.core.parser.node.AFinSubsetExpression;
import de.be4.classicalb.core.parser.node.AFirstExpression;
import de.be4.classicalb.core.parser.node.AFirstProjectionExpression;
import de.be4.classicalb.core.parser.node.AFrontExpression;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AGeneralConcatExpression;
import de.be4.classicalb.core.parser.node.AGeneralIntersectionExpression;
import de.be4.classicalb.core.parser.node.AGeneralProductExpression;
import de.be4.classicalb.core.parser.node.AGeneralSumExpression;
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
import de.be4.classicalb.core.parser.node.ALastExpression;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.ALessPredicate;
import de.be4.classicalb.core.parser.node.AMaxExpression;
import de.be4.classicalb.core.parser.node.AMinExpression;
import de.be4.classicalb.core.parser.node.AMinIntExpression;
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
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASizeExpression;
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
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.btypes.BType;
import de.tlc4b.btypes.FunctionType;
import de.tlc4b.btypes.IntegerType;
import de.tlc4b.btypes.SetType;
import de.tlc4b.tla.TLAModule;

public class UsedStandardModules extends DepthFirstAdapter {
	private enum StandardModule {
		Naturals, Integers, FiniteSets, Sequences, TLC, BBuiltIns, Relations, FunctionsAsRelations, Functions, SequencesExtended, SequencesAsRelations, ExternalFunctions, Foo
	}

	private final static ArrayList<StandardModule> modules = new ArrayList<>();
	static {
		modules.add(StandardModule.Naturals);
		modules.add(StandardModule.Integers);
		modules.add(StandardModule.FiniteSets);
		modules.add(StandardModule.Sequences);
		modules.add(StandardModule.TLC);
		modules.add(StandardModule.BBuiltIns);
		modules.add(StandardModule.Relations);
		modules.add(StandardModule.Functions);
		modules.add(StandardModule.FunctionsAsRelations);
		modules.add(StandardModule.SequencesExtended);
		modules.add(StandardModule.SequencesAsRelations);
		modules.add(StandardModule.ExternalFunctions);
	}

	private final Set<StandardModule> extendedStandardModules;
	private final Typechecker typechecker;

	public UsedStandardModules(Start start, Typechecker typechecker,
			TypeRestrictor typeRestrictor, TLAModule tlaModule) {
		this.extendedStandardModules = new HashSet<>();
		this.typechecker = typechecker;

		if (TLC4BGlobals.useSymmetry()) {
			extendedStandardModules.add(StandardModule.TLC);
		}

		List<PDefinition> definitions = tlaModule.getAllDefinitions();
		if (definitions != null) {
			for (PDefinition pDefinition : definitions) {
				pDefinition.apply(this);
			}
		}
		for (Node node : typeRestrictor.getAllRestrictedNodes()) {
			node.apply(this);
		}

		start.apply(this);
	}

	public List<String> getExtendedModules() {
		ArrayList<StandardModule> list = new ArrayList<>(extendedStandardModules);
		if (list.contains(StandardModule.Integers)) {
			list.remove(StandardModule.Naturals);
		}
		list.sort((s1, s2) -> {
			Integer i1 = modules.indexOf(s1);
			Integer i2 = modules.indexOf(s2);
			return i1.compareTo(i2);
		});
		return list.stream().map(StandardModule::name).collect(Collectors.toList());
	}

	public Set<String> getStandardModulesToBeCreated() {
		// dependencies of standard modules
		HashSet<StandardModule> res = new HashSet<>();
		for (StandardModule module : extendedStandardModules) {
			switch (module) {
			case ExternalFunctions:
				res.add(StandardModule.ExternalFunctions);
				break;
			case FunctionsAsRelations:
				res.add(StandardModule.FunctionsAsRelations);
				res.add(StandardModule.Functions);
				break;
			case SequencesAsRelations:
				res.add(StandardModule.SequencesAsRelations);
				res.add(StandardModule.Relations);
				res.add(StandardModule.FunctionsAsRelations);
				res.add(StandardModule.Functions);
				break;
			case BBuiltIns:
				res.add(StandardModule.BBuiltIns);
				break;
			case Functions:
				res.add(StandardModule.Functions);
				break;
			case Relations:
				res.add(StandardModule.Relations);
				break;
			case Sequences:
				break;
			case SequencesExtended:
				res.add(StandardModule.SequencesExtended);
				break;
			default:
				break;
			}

		}
		return res.stream().map(StandardModule::name).collect(Collectors.toSet());
	}

	@Override
	public void inAExpressionDefinitionDefinition(AExpressionDefinitionDefinition node) {
		if (TLC4BGlobals.isForceTLCToEvalConstants()) {
			extendedStandardModules.add(StandardModule.TLC);
		}
		String name = node.getName().getText().trim();
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			extendedStandardModules.add(StandardModule.ExternalFunctions);
		}
	}

	@Override
	public void inADefinitionPredicate(ADefinitionPredicate node) {
		String name = node.getDefLiteral().getText().trim();
		if (StandardModules.isKeywordInModuleExternalFunctions(name)) {
			extendedStandardModules.add(StandardModule.ExternalFunctions);
		}
	}

	/**
	 * Naturals
	 */

	@Override
	public void caseANaturalSetExpression(ANaturalSetExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	@Override
	public void caseANatural1SetExpression(ANatural1SetExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	@Override
	public void caseANatSetExpression(ANatSetExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	@Override
	public void caseANat1SetExpression(ANat1SetExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inALessEqualPredicate(ALessEqualPredicate node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inALessPredicate(ALessPredicate node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inAGreaterEqualPredicate(AGreaterEqualPredicate node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inAGreaterPredicate(AGreaterPredicate node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inAAddExpression(AAddExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}

	public void inAIntervalExpression(AIntervalExpression node) {
		extendedStandardModules.add(StandardModule.Naturals);
	}


	public void inAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		BType t = typechecker.getType(node);
		if (t instanceof IntegerType) {
			extendedStandardModules.add(StandardModule.Naturals);
		}
	}

	public void inAMultOrCartExpression(AMultOrCartExpression node) {
		BType t = typechecker.getType(node);
		if (t instanceof IntegerType) {
			extendedStandardModules.add(StandardModule.Naturals);
		} else {
			// usedStandardModules.add(StandardModule.RelationsNew);
		}
	}

	/**
	 * Integers
	 */

	public void inAIntSetExpression(AIntSetExpression node) {
		extendedStandardModules.add(StandardModule.Integers);
	}

	public void inAIntegerSetExpression(AIntegerSetExpression node) {
		extendedStandardModules.add(StandardModule.Integers);
	}

	public void inAUnaryMinusExpression(AUnaryMinusExpression node) {
		extendedStandardModules.add(StandardModule.Integers);
	}

	public void inAMinIntExpression(AMinIntExpression node) {
		extendedStandardModules.add(StandardModule.Integers);
	}

	/**
	 * FiniteSets
	 */
	public void inACardExpression(ACardExpression node) {
		extendedStandardModules.add(StandardModule.FiniteSets);
	}

	/**
	 * BBuiltIns
	 */

	public void inAPowerOfExpression(APowerOfExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}
	
	public void inAMinExpression(AMinExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAMaxExpression(AMaxExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAModuloExpression(AModuloExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}
	
	public void inADivExpression(ADivExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}
	
	public void inAGeneralSumExpression(AGeneralSumExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAGeneralProductExpression(AGeneralProductExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inASuccessorExpression(ASuccessorExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAPredecessorExpression(APredecessorExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAPow1SubsetExpression(APow1SubsetExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAFinSubsetExpression(AFinSubsetExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAFin1SubsetExpression(AFin1SubsetExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inANotSubsetPredicate(ANotSubsetPredicate node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inANotSubsetStrictPredicate(ANotSubsetStrictPredicate node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAGeneralIntersectionExpression(
			AGeneralIntersectionExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAQuantifiedIntersectionExpression(
			AQuantifiedIntersectionExpression node) {
		extendedStandardModules.add(StandardModule.BBuiltIns);
	}

	public void inAQuantifiedUnionExpression(AQuantifiedUnionExpression node) {
		// usedStandardModules.add(StandardModule.BBuiltIns);
	}

	/**
	 * Functions
	 */
	private void setOfFunctions(Node node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.Functions);
		} else {
			extendedStandardModules.add(StandardModule.FunctionsAsRelations);
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
		// System.out.println(node.parent().getClass());
		if (node.parent() instanceof AAssignSubstitution) {
			AAssignSubstitution parent = (AAssignSubstitution) node.parent();
			if (parent.getLhsExpression().contains(node)) {
				// function assignment (function call on the left side), e.g.
				// f(x) := 1
				return;
			}
		}
		BType type = typechecker.getType(node.getIdentifier());
		if (type instanceof SetType) {
			extendedStandardModules.add(StandardModule.FunctionsAsRelations);
		}

	}

	public void inATotalFunctionExpression(ATotalFunctionExpression node) {
		SetType type = (SetType) typechecker.getType(node);
		if (type.getSubtype() instanceof SetType) {
			extendedStandardModules.add(StandardModule.FunctionsAsRelations);
		}
	}

	/**
	 * Relations
	 */

	private void evalFunctionOrRelation(Node node) {
		BType t = typechecker.getType(node);
		if (t instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.Functions);
		} else {
			extendedStandardModules.add(StandardModule.Relations);
		}
	}

	public void inARelationsExpression(ARelationsExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inADomainExpression(ADomainExpression node) {
		BType t = typechecker.getType(node.getExpression());
		if (!(t instanceof FunctionType)) {
			extendedStandardModules.add(StandardModule.Relations);
		}
	}

	public void inASetExtensionExpression(ASetExtensionExpression node) {
		BType t = typechecker.getType(node);
		if (t instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.TLC);
		}
	}

	public void inARangeExpression(ARangeExpression node) {
		evalFunctionOrRelation(node.getExpression());
	}

	public void inAImageExpression(AImageExpression node) {
		evalFunctionOrRelation(node.getLeft());
	}

	public void inAIdentityExpression(AIdentityExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inADomainRestrictionExpression(ADomainRestrictionExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inADomainSubtractionExpression(ADomainSubtractionExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inARangeRestrictionExpression(ARangeRestrictionExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inARangeSubtractionExpression(ARangeSubtractionExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inAReverseExpression(AReverseExpression node) {
		evalFunctionOrRelation(node.getExpression());
	}

	public void inAOverwriteExpression(AOverwriteExpression node) {
		evalFunctionOrRelation(node);
	}

	public void inAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<>(node.getLhsExpression());
		for (PExpression e : copy) {
			if (e instanceof AFunctionExpression) {
				BType type = typechecker.getType(((AFunctionExpression) e)
						.getIdentifier());
				if (type instanceof SetType) {
					extendedStandardModules.add(StandardModule.Relations);
				} else {
					extendedStandardModules.add(StandardModule.Functions);
				}
			}
		}
	}

	public void inADirectProductExpression(ADirectProductExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inAParallelProductExpression(AParallelProductExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inACompositionExpression(ACompositionExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inAFirstProjectionExpression(AFirstProjectionExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inASecondProjectionExpression(ASecondProjectionExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inAIterationExpression(AIterationExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inAClosureExpression(AClosureExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inAReflexiveClosureExpression(AReflexiveClosureExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inATransFunctionExpression(ATransFunctionExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	public void inATransRelationExpression(ATransRelationExpression node) {
		extendedStandardModules.add(StandardModule.Relations);
	}

	/**
	 * Sequences
	 */

	public void inASeqExpression(ASeqExpression node) {
		SetType type = (SetType) typechecker.getType(node);
		if (type.getSubtype() instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.Sequences);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inASizeExpression(ASizeExpression node) {
		evalSequenceOrRelation(node.getExpression());
	}

	public void inAConcatExpression(AConcatExpression node) {
		evalSequenceOrRelation(node);
	}

	private void evalSequenceOrRelation(Node node) {
		BType type = typechecker.getType(node);
		if (type instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.Sequences);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inAFirstExpression(AFirstExpression node) {
		evalSequenceOrRelation(node.getExpression());
	}

	public void inATailExpression(ATailExpression node) {
		evalSequenceOrRelation(node.getExpression());
	}

	/**
	 * SequencesExtended
	 */

	private void evalSequenceExtendedOrRelation(Node node) {
		BType type = typechecker.getType(node);
		if (type instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.SequencesExtended);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inAIseqExpression(AIseqExpression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.SequencesExtended);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inASeq1Expression(ASeq1Expression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.SequencesExtended);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inAIseq1Expression(AIseq1Expression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof FunctionType) {
			extendedStandardModules.add(StandardModule.SequencesExtended);
		} else {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		}
	}

	public void inAInsertFrontExpression(AInsertFrontExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

	public void inALastExpression(ALastExpression node) {
		evalSequenceExtendedOrRelation(node.getExpression());
	}

	public void inAFrontExpression(AFrontExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

	public void inAPermExpression(APermExpression node) {
		SetType set = (SetType) typechecker.getType(node);
		if (set.getSubtype() instanceof SetType) {
			extendedStandardModules.add(StandardModule.SequencesAsRelations);
		} else {
			extendedStandardModules.add(StandardModule.SequencesExtended);
		}
	}

	public void inARevExpression(ARevExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

	public void inAGeneralConcatExpression(AGeneralConcatExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

	public void inARestrictFrontExpression(ARestrictFrontExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

	public void inARestrictTailExpression(ARestrictTailExpression node) {
		evalSequenceExtendedOrRelation(node);
	}

}
