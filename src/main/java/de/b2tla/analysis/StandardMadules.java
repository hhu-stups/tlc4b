package de.b2tla.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class StandardMadules {

	// Functions

	public static final String RANGE = "Range";
	public static final String PARTIAL_FUNCTION = "PartialFunction";
	public static final String INJECTIVE_TOTAL_FUNCTION = "ITotalFunc";
	public static final String INJECTIVE_PARTIAL_FUNCTION = "IParFunc";

	// Relations
	public static final String REL_CALL = "RelCall";
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
	public static final String REL_OVERRIDING = "RelOver";
	public static final String REL_DIRECT_PRODUCT = "RelDirectProduct";
	public static final String REL_COMPOSITION = "RelComposition";
	public static final String PROJECTION_FUNCTION_FIRST = "Prj1";
	public static final String PROJECTION_FUNCTION_SECOND = "Prj2";
	public static final String CLOSURE1 = "Closure1";
	public static final String CLOSURE = "Closure";

	public static final String REL_TOTAL_FUNCTION = "RelTotalFunc";
	public static final String REL_TOTAL_FUNCTION_ELEMENT_OF = "RelTotalFuncEleOf";
	
	public static final String REL_INJECTIVE_TOTAL_FUNCTION = "RelITotalFunc";
	public static final String REL_PARTIAL_FUNCTION = "RelParFunc";
	public static final String REL_INJECTIVE_PARTIAL_FUNCTION = "RelIParFunc";

	
	public static final String BIJECTIVE_FUNCTION = "BijFunc";
	public static final String REL_BIJECTIVE_FUNCTION = "RelBijFunc";
	
	
	public static final String TOTAL_SURJECTIVE_FUNCTION = "TotalSurFunc";
	public static final String REL_TOTAL_SURJECTIVE_FUNCTION = "RelTotalSurFunc";
	public static final String REL_TOTAL_SURJECTIVE_FUNCTION_ELEMENT_OF = "RelTotalSurFuncEleOf";
	
	public static final String INJECTIVE_SEQUENCES = "ISeq";
	public static final String NOT_EMPTY_INJECTIVE_SEQUENCES = "ISeq1";
	
	public static final String SEQ_CONCATINATION = "Concat";
	
	public static final String REL_INJECTIVE_SEQUENCES = "RelISeq";
	public static final String REL_NOT_EMPTY_INJECTIVE_SEQUENCES = "RelISeq1";
	
	public static final String REL_CLOSURE = "RelClosure";
	
	public static final ArrayList<String> Relations = new ArrayList<String>();

	static {
		Relations.add(REL_CALL);
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
		Relations.add(PROJECTION_FUNCTION_FIRST);
		Relations.add(PROJECTION_FUNCTION_SECOND);
		Relations.add(CLOSURE1);
		Relations.add(CLOSURE);
		Relations.add(REL_TOTAL_FUNCTION);
		Relations.add(REL_INJECTIVE_TOTAL_FUNCTION);
		Relations.add(REL_PARTIAL_FUNCTION);

	}

}
