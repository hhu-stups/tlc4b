package de.tlc4b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;


public final class StandardModules {

	private StandardModules() {
	}

	// Functions
	public static final String FUNC_RANGE = "Range";
	public static final String FUNC_IMAGE = "Image";
	public static final String FUNC_ID = "Id";
	public static final String FUNC_INVERSE = "Inverse";
	public static final String FUNC_DOMAIN_RESTRICTION = "DomRes";
	public static final String FUNC_DOMAIN_SUBTRACTION = "DomSub";
	public static final String FUNC_RANGE_RESTRICTION = "RanRes";
	public static final String FUNC_RANGE_SUBTRACTION = "RanSub";
	public static final String FUNC_OVERRIDE = "Override";
	public static final String FUNC_ASSIGN = "FuncAssign";

	private static final ArrayList<String> functions = new ArrayList<>();
	static {
		functions.add(FUNC_RANGE);
		functions.add(FUNC_ID);
		functions.add(FUNC_INVERSE);
		functions.add(FUNC_DOMAIN_RESTRICTION);
		functions.add(FUNC_DOMAIN_SUBTRACTION);
		functions.add(FUNC_RANGE_RESTRICTION);
		functions.add(FUNC_RANGE_SUBTRACTION);
		functions.add(FUNC_OVERRIDE);
		functions.add(FUNC_ASSIGN);
	}

	public static boolean isKeywordInModuleFunctions(String name) {
		return functions.contains(name);
	}

	public static final String TOTAL_INJECTIVE_FUNCTION = "TotalInjFunc";
	public static final String TOTAL_SURJECTIVE_FUNCTION = "TotalSurFunc";
	public static final String TOTAL_BIJECTIVE_FUNCTION = "TotalBijFunc";

	/** Sets of Partial functions **/
	public static final String PARTIAL_FUNCTION = "ParFunc";
	public static final String PARTIAL_FUNCTION_ELEMENT_OF = "ParFuncEleOf";
	public static final String ELEMENT_OF_PARTIAL_FUNCTION = "isEleOfParFunc";

	// injective
	public static final String PARTIAL_INJECTIVE_FUNCTION = "ParInjFunc";
	public static final String PARTIAL_INJECTIVE_FUNCTION_ELEMENT_OF = "ParInjFuncEleOf";
	// surjective
	public static final String PARTIAL_SURJECTIVE_FUNCTION = "ParSurFunc";
	public static final String PARTIAL_SURJECTIVE_FUNCTION_ELEMENT_OF = "ParSurFuncEleOf";
	// bijective
	public static final String PARTIAL_BIJECTIVE_FUNCTION = "ParBijFunc";
	public static final String PARTIAL_BIJECTIVE_FUNCTION_ELEMENT_OF = "ParBijFuncEleOf";

	// Relations
	public static final String RELATIONS = "Relations";
	public static final String REL_DOMAIN = "RelDomain";
	public static final String REL_RANGE = "RelRange";
	public static final String REL_ID = "RelId";
	public static final String REL_DOMAIN_RESTRICTION = "RelDomRes";
	public static final String REL_DOMAIN_SUBTRACTION = "RelDomSub";
	public static final String REL_RANGE_RESTRICTION = "RelRanRes";
	public static final String REL_RANGE_SUBTRACTION = "RelRanSub";
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
	public static final String REL_CALL_WITHOUT_WD_CHECK = "RelCallWithoutWDCheck";

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

	private final static Set<String> SequencesKeywords = new HashSet<>();
	static {
		SequencesKeywords.add("Seq");
		SequencesKeywords.add("Len");
		SequencesKeywords.add("Append");
		SequencesKeywords.add("Head");
		SequencesKeywords.add("Tail");
		SequencesKeywords.add("Subseq");
		SequencesKeywords.add("SelectSeq");
	}

	public static boolean isKeywordInModuleSequences(String name) {
		return SequencesKeywords.contains(name);
	}

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
	public static final String SEQUENCE_GENERAL_CONCATENATION = "Conc";
	public static final String SEQUENCE_TAKE_FIRST_ELEMENTS = "TakeFirstElements";
	public static final String SEQUENCE_DROP_FIRST_ELEMENTS = "DropFirstElements";

	private final static Set<String> SequencesExtendedKeywords = new HashSet<>();
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
		SequencesExtendedKeywords.add(SEQUENCE_GENERAL_CONCATENATION);
		SequencesExtendedKeywords.add(SEQUENCE_TAKE_FIRST_ELEMENTS);
		SequencesExtendedKeywords.add(SEQUENCE_DROP_FIRST_ELEMENTS);
	}

	public static boolean isKeywordInModuleSequencesExtended(String name) {
		return SequencesExtendedKeywords.contains(name);
	}

	// SequencesAsRelations
	public static final String REL_SEQUENCE_SIZE = "RelSeqSize";
	public static final String IS_REL_SEQUENCE = "isRelSeq";
	public static final String REL_SEQUENCE_SET = "RelSeqSet";
	public static final String REL_SET_OF_SEQUENCES = "RelSeq";
	public static final String REL_SET_OF_NON_EMPTY_SEQUENCES = "RelSeq1";
	public static final String IS_REL_SEQUENCE_1 = "isRelSeq1";
	public static final String REL_SEQUENCE_1_SET = "RelSeqSet1";
	public static final String REL_INJECTIVE_SEQUENCE = "RelISeq";
	public static final String REL_INJECTIVE_SEQUENCE_ELEMENT_OF = "RelISeqEleOf";
	public static final String REL_INJECTIVE_SEQUENCE_1 = "RelISeq1";
	public static final String REL_INJECTIVE_SEQUENCE_1_ELEMENT_OF = "RelISeq1EleOf";
	public static final String REL_SEQUENCE_Concat = "RelSeqConcat";
	public static final String REL_SEQUENCE_PREPEND = "RelSeqPrepend";
	public static final String REL_SEQUENCE_APPEND = "RelSeqAppend";
	public static final String REL_SEQUENCE_REVERSE = "RelSeqReverse";
	public static final String REL_SEQUENCE_FIRST_ELEMENT = "RelSeqFirst";
	public static final String REL_SEQUENCE_LAST_ELEMENT = "RelSeqLast";
	public static final String REL_SEQUENCE_FRONT = "RelSeqFront";
	public static final String REL_SEQUENCE_TAIL = "RelSeqTail";
	public static final String REL_SEQUENCE_PERM = "RelSeqPerm";
	public static final String REL_SEQUENCE_GENERAL_CONCATENATION = "RelSeqConc";
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
	public static final String B_POWER_Of = "BPowerOf";
	public static final String B_MODULO = "BModulo";
	public static final String B_DIVISION = "BDivision";

	public static final String GENERAL_SUMMATION = "Sigma";
	public static final String GENERAL_PRODUCT = "Pi";

	private static final ArrayList<String> Relations = new ArrayList<>();
	static {
		Relations.add(RELATIONS);
		Relations.add(REL_DOMAIN);
		Relations.add(REL_RANGE);
		Relations.add(REL_ID);
		Relations.add(REL_DOMAIN_RESTRICTION);
		Relations.add(REL_DOMAIN_SUBTRACTION);
		Relations.add(REL_RANGE_RESTRICTION);
		Relations.add(REL_RANGE_SUBTRACTION);
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

	public static boolean containsNameFromModuleRelations(String name) {
		return Relations.contains(name);
	}

	/*
	 * External Functions
	 * 
	 * All external functions must be defined in the standard module
	 * ExternalFunctions.tla (src/main/resources/standardModules/). The B
	 * machine must contain a definition declaring the external function. The
	 * typing definition (e.g. EXTERNAL_FUNCTION_STRING_SPLIT ==
	 * ((STRING*STRING) --> (INTEGER<->STRING));) is not mandatory.
	 * 
	 * The B definitions will be ignored in the {@link TLAPrinter}.
	 */

	public static final String EXTERNAL_printf = "printf";
	public static final String INT_TO_STRING = "INT_TO_STRING";
	public static final String STRING_SPLIT = "STRING_SPLIT";
	public static final String SORT_SET = "SORT_SET";
	public static final String STRING_APPEND = "STRING_APPEND";
	public static final String STRING_TO_INT = "STRING_TO_INT";
	public static final String DECIMAL_TO_INT = "DECIMAL_TO_INT";

	private static final ArrayList<String> ExternalFunctions = new ArrayList<>();
	static {
		ExternalFunctions.add(EXTERNAL_printf);
		ExternalFunctions.add(INT_TO_STRING);
		ExternalFunctions.add(STRING_SPLIT);
		ExternalFunctions.add(STRING_APPEND);
		ExternalFunctions.add(STRING_TO_INT);

		ExternalFunctions.add(SORT_SET);
		ExternalFunctions.add(DECIMAL_TO_INT);
	}

	public static boolean isAbstractConstant(String name) {
		return name.equals(SORT_SET) || name.equals(DECIMAL_TO_INT);

	}

	public static boolean isKeywordInModuleExternalFunctions(String name) {
		return ExternalFunctions.contains(name);
	}

}
