package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class StandardMadules {

	// Functions
	public static final String FUNC_RANGE = "Range";
	public static final String FUNC_IMAGE = "Image";
	public static final String FUNC_ID = "Id";
	public static final String FUNC_INVERSE = "Inverse";
	public static final String FUNC_DOMAIN_RESTRICTION = "DomRes";
	public static final String FUNC_DOMAIN_SUBSTRACTION = "DomSub";
	public static final String FUNC_RANGE_RESTRICTION = "RanRes";
	public static final String FUNC_RANGE_SUBSTRACTION = "RanSub";
	public static final String FUNC_OVERRIDE = "Override";
	public static final String FUNC_ASSIGN = "FuncAssign";

	
	
	public static ArrayList<String> functions = new ArrayList<String>();
	static {
		functions.add(FUNC_RANGE);
		functions.add(FUNC_ID);
		functions.add(FUNC_INVERSE);
		functions.add(FUNC_DOMAIN_RESTRICTION);
		functions.add(FUNC_DOMAIN_SUBSTRACTION);
		functions.add(FUNC_RANGE_RESTRICTION);
		functions.add(FUNC_RANGE_SUBSTRACTION);
		functions.add(FUNC_OVERRIDE);
		functions.add(FUNC_ASSIGN);
	}

	public static final String TOTAL_INJECTIVE_FUNCTION = "TotalInjFunc";
	public static final String TOTAL_SURJECTIVE_FUNCTION = "TotalSurFunc";
	public static final String TOTAL_BIJECTIVE_FUNCTION = "TotalBijFunc";

	public static final String PARTIAL_FUNCTION = "ParFunc";
	public static final String PARTIAL_INJECTIVE_FUNCTION = "ParInjFunc";
	public static final String PARTIAL_SURJECTIVE_FUNCTION = "ParSurFunc";
	public static final String PARITAL_BIJECTIVE_FUNCTION = "ParBijFunc";

	// Relations
	public static final String RELATIONS = "Relations";
	public static final String REL_DOMAIN = "RelDomain";
	public static final String REL_RANGE = "RelRange";
	public static final String REL_ID = "RelId";
	public static final String REL_DOMAIN_RESTRICTION = "RelDomRes";
	public static final String REL_DOMAIN_SUBSTRACTION = "RelDomSub";
	public static final String REL_RANGE_RESTRICTION = "RelRanRes";
	public static final String REL_RANGE_SUBSTRACTION = "RelRanSub";
	public static final String REL_INVERSE = "RelInverse";
	public static final String REL_IMAGE = "RelImage";
	public static final String REL_OVERRIDING = "RelOverride";
	public static final String REL_OVERRIDING_FUNC = "RelOverrideFunc";
	public static final String REL_DIRECT_PRODUCT = "RelDirectProduct";
	public static final String REL_PARALLEL_PRODUCT = "RelParallelProduct";
	public static final String REL_COMPOSITION = "RelComposition";
	public static final String REL_PROJECTION_FUNCTION_FIRST = "RelPrj1";
	public static final String REL_PROJECTION_FUNCTION_SECOND = "RelPrj2";
	public static final String REL_ITERATE = "RelIterate";
	public static final String REL_CLOSURE1 = "RelClosure1";
	public static final String REL_CLOSURE = "RelClosure";
	public static final String REL_FNC = "RelFnc";
	public static final String REL_REL = "RelRel";

	// FunctionsAsRelations
	public static final String REL_CALL = "RelCall";

	public static final String REL_TOTAL_FUNCTION = "RelTotalFunc";
	public static final String REL_TOTAL_FUNCTION_ELEMENT_OF = "RelTotalFuncEleOf";

	public static final String REL_TOTAL_INJECTIVE_FUNCTION = "RelTotalInjFunc";
	public static final String REL_TOTAL_INJECTIVE_FUNCTION_ELEMENT_OF = "RelTotalInjFuncEleOf";

	public static final String REL_TOTAL_SURJECTIVE_FUNCTION = "RelTotalSurFunc";
	public static final String REL_TOTAL_SURJECTIVE_FUNCTION_ELEMENT_OF = "RelTotalSurFuncEleOf";

	public static final String REL_TOTAL_BIJECTIVE_FUNCTION = "RelTotalBijFunc";
	public static final String REL_TOTAL_BIJECTIVE_FUNCTION_ELEMENT_OF = "RelTotalBijFuncEleOf";

	public static final String REL_PARTIAL_FUNCTION = "RelParFunc";
	public static final String REL_PARTIAL_FUNCTION_ELEMENT_OF = "RelParFuncEleOf";

	public static final String REL_PARTIAL_INJECTIVE_FUNCTION = "RelParInjFunc";
	public static final String REL_PARTIAL_INJECTIVE_FUNCTION_ELEMENT_OF = "RelParInjFuncEleOf";

	public static final String REL_PARTIAL_SURJECTIVE_FUNCTION = "RelParSurFunc";
	public static final String REL_PARTIAL_SURJECTIVE_FUNCTION_ELEMENT_OF = "RelParSurFuncEleOf";

	public static final String REL_PARTIAL_BIJECTIVE_FUNCTION = "RelParBijFunc";
	public static final String REL_PARTIAL_BIJECTIVE_FUNCTION_ELEMENT_OF = "RelParBijFuncEleOf";

	// SequencesExtended
	public static final String SEQUENCE_LAST_ELEMENT = "Last";
	public static final String SEQUENCE_PREPEND_ELEMENT = "Prepend";
	public static final String SEQUENCE_FRONT = "Front";
	public static final String SEQUENCE_1 = "Seq1";
	public static final String INJECTIVE_SEQUENCE = "ISeq";
	public static final String INJECTIVE_SEQUENCE_ELEMENT_OF = "ISeqEleOf";
	public static final String INJECTIVE_SEQUENCE_1 = "ISeq1";
	public static final String INJECTIVE_SEQUENCE_1_ELEMENT_OF = "ISeq1EleOf";
	public static final String SEQUENCE_PERMUTATION = "Perm";
	public static final String SEQUENCE_REVERSE = "Reverse";
	public static final String SEQUENCE_GENERAL_CONCATINATION = "Conc";
	public static final String SEQUENCE_TAKE_FIRST_ELEMENTS = "TakeFirstElements";
	public static final String SEQUENCE_DROP_FIRST_ELEMENTS = "DropFirstElements";

	public final static Set<String> SequencesExtendedKeywords = new HashSet<String>();
	static {
		SequencesExtendedKeywords.add(SEQUENCE_LAST_ELEMENT);
		SequencesExtendedKeywords.add(SEQUENCE_PREPEND_ELEMENT);
		SequencesExtendedKeywords.add(SEQUENCE_FRONT);
		SequencesExtendedKeywords.add(SEQUENCE_1);
		SequencesExtendedKeywords.add(INJECTIVE_SEQUENCE);
		SequencesExtendedKeywords.add(INJECTIVE_SEQUENCE_ELEMENT_OF);
		SequencesExtendedKeywords.add(INJECTIVE_SEQUENCE_1);
		SequencesExtendedKeywords.add(INJECTIVE_SEQUENCE_1_ELEMENT_OF);
		SequencesExtendedKeywords.add(SEQUENCE_PERMUTATION);
		SequencesExtendedKeywords.add(SEQUENCE_REVERSE);
		SequencesExtendedKeywords.add(SEQUENCE_GENERAL_CONCATINATION);
		SequencesExtendedKeywords.add(SEQUENCE_TAKE_FIRST_ELEMENTS);
		SequencesExtendedKeywords.add(SEQUENCE_DROP_FIRST_ELEMENTS);
	}
	
	// SequencesAsRelations
	public static final String REL_SEQUENCE_SIZE = "RelSeqSize";
	public static final String IS_REL_SEQUENCE = "isRelSeq";
	public static final String REL_SEQUENCE_SET = "RelSeqSet";
	public static final String IS_REL_SEQUENCE_1 = "isRelSeq1";
	public static final String REL_SEQUENCE_1_SET = "RelSeqSet1";
	public static final String REL_INJECTIVE_SEQUENCE = "RelISeq";
	public static final String REL_INJECTIVE_SEQUENCE_1 = "RelISeq1";
	public static final String REL_SEQUENCE_Concat = "RelSeqConcat";
	public static final String REL_SEQUENCE_PREPAND = "RelSeqPrepand";
	public static final String REL_SEQUENCE_APPEND = "RelSeqAppend";
	public static final String REL_SEQUENCE_REVERSE = "RelSeqReverse";
	public static final String REL_SEQUENCE_FIRST_ELEMENT = "RelSeqFirst";
	public static final String REL_SEQUENCE_LAST_ELEMENT = "RelSeqLast";
	public static final String REL_SEQUENCE_FRONT = "RelSeqFront";
	public static final String REL_SEQUENCE_TAIL = "RelSeqTail";
	public static final String REL_SEQUENCE_PERM = "RelSeqPerm";
	public static final String REL_SEQUENCE_GENERAL_CONCATINATION = "RelSeqConc";
	public static final String REL_SEQUENCE_TAKE_FIRST_ELEMENTS = "RelSeqTakeFirstElements";
	public static final String REL_SEQUENCE_DROP_FIRST_ELEMENTS = "RelSeqDropFirstElements";

	/*
	 * BBuiltIns
	 */

	public static final String MIN = "Min";
	public static final String MAX = "Max";
	public static final String NOT_SUBSET = "NotSubset";
	public static final String NOT_STRICT_SUBSET = "NotStrictSubset";
	public static final String POW_1 = "Pow1";
	public static final String FINITE_SUBSETS = "Fin";
	public static final String FINITE_1_SUBSETS = "Fin1";

	public static final String GENERAL_SUMMATION = "Sigma";
	public static final String GENERAL_PRODUCT = "Pi";

	public static final ArrayList<String> Relations = new ArrayList<String>();

	static {
		Relations.add(RELATIONS);
		Relations.add(REL_DOMAIN);
		Relations.add(REL_RANGE);
		Relations.add(REL_ID);
		Relations.add(REL_DOMAIN_RESTRICTION);
		Relations.add(REL_DOMAIN_SUBSTRACTION);
		Relations.add(REL_RANGE_RESTRICTION);
		Relations.add(REL_RANGE_SUBSTRACTION);
		Relations.add(REL_INVERSE);
		Relations.add(REL_IMAGE);
		Relations.add(REL_OVERRIDING);
		Relations.add(REL_DIRECT_PRODUCT);
		Relations.add(REL_COMPOSITION);
		Relations.add(REL_PROJECTION_FUNCTION_FIRST);
		Relations.add(REL_PROJECTION_FUNCTION_SECOND);
		Relations.add(REL_CLOSURE1);
		Relations.add(REL_CLOSURE);
		Relations.add(REL_TOTAL_FUNCTION);
		Relations.add(REL_TOTAL_INJECTIVE_FUNCTION);
		Relations.add(REL_PARTIAL_FUNCTION);

	}

}
