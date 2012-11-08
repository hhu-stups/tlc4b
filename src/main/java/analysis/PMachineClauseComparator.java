package analysis;

import java.util.Comparator;
import java.util.Hashtable;

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
import de.be4.classicalb.core.parser.node.PMachineClause;

public class PMachineClauseComparator implements Comparator<PMachineClause>{

	private static Hashtable<Object, Integer> priority = new Hashtable<Object, Integer>();
	static{
		//declarations clauses
		priority.put(ADefinitionsMachineClause.class, 10);
		priority.put(ASeesMachineClause.class, 10);
		priority.put(ASetsMachineClause.class, 9);
		priority.put(AConstantsMachineClause.class, 8);
		priority.put(AVariablesMachineClause.class, 7);
		priority.put(AConcreteVariablesMachineClause.class, 6);
		

		// properties clauses 
		priority.put(AConstraintsMachineClause.class, 5);
		priority.put(APropertiesMachineClause.class, 4);
		priority.put(AInvariantMachineClause.class, 3);
		priority.put(AAssertionsMachineClause.class, 2);
		priority.put(AOperationsMachineClause.class, 1);
		priority.put(AInitialisationMachineClause.class, 0);
	}
	
	
	@Override
	public int compare(PMachineClause arg0, PMachineClause arg1) {
		if(priority.get(arg0.getClass()).intValue() < priority.get(arg1.getClass()).intValue()){
			return 1;
		}
		if(priority.get(arg0.getClass()).intValue() > priority.get(arg1.getClass()).intValue()){
			return -1;
		}
		
		return 0;
	}
	
}
