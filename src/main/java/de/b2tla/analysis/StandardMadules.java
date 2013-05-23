package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class StandardMadules {

	// Functions
	public static final String RANGE = "Range";
	public static final String IMAGE = "Image";
	
	public static final String TOTAL_INJECTIVE_FUNCTION = "TotalInjFunc";
	public static final String TOTAL_SURJECTIVE_FUNCTION = "TotalSurFunc";
	public static final String TOTAL_BIJECTIVE_FUNCTION = "TotalBijFunc";

	public static final String PARTIAL_FUNCTION = "ParFunc";
	public static final String PARTIAL_INJECTIVE_FUNCTION = "ParInjFunc";
	public static final String PARTIAL_SURJECTIVE_FUNCTION = "ParSurFunc";
	public static final String PARITAL_BIJECTIVE_FUNCTION = "ParBijFunc";
	
	// Relations
	public static final String RELATION = "Relation";
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
	public static final String SEQUENCE_REVERSE = "Rev";
	public static final String SEQUENCE_GENERAL_CONCATINATION = "Conc";
	
	public static final String SEQUENCE_TAKE_FIRST_ELEMENTS = "TakeFirstElements";
	public static final String SEQUENCE_DROP_FIRST_ELEMENTS = "DropFirstElements";
	
	
	public static final String REL_INJECTIVE_SEQUENCES = "RelISeq";
	public static final String REL_NOT_EMPTY_INJECTIVE_SEQUENCES = "RelISeq1";
	
	
	public static final ArrayList<String> Relations = new ArrayList<String>();

	static {
		Relations.add(RELATION);
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
