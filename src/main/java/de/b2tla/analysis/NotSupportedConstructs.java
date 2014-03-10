package de.b2tla.analysis;

import de.b2tla.exceptions.NotSupportedException;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACaseSubstitution;
import de.be4.classicalb.core.parser.node.ASequenceSubstitution;
import de.be4.classicalb.core.parser.node.AWhileSubstitution;
import de.be4.classicalb.core.parser.node.Start;

public class NotSupportedConstructs extends DepthFirstAdapter{
	
	public NotSupportedConstructs(Start start){
		start.apply(this);
	}
	
    public void inAWhileSubstitution(AWhileSubstitution node)
    {
    	throw new NotSupportedException("While substitutions are currently not supported.");
    }
    
    public void inACaseSubstitution(ACaseSubstitution node)
    {
    	throw new NotSupportedException("Case substitutions are currently not supported.");
    }
    
    public void inASequenceSubstitution(ASequenceSubstitution node)
    {
    	throw new NotSupportedException("Sequence substitutions ';' are currently not supported.");
    }
    

}
