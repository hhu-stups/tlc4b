package b2tla.analysis.transformation;

import java.util.ArrayList;
import java.util.Hashtable;

import b2tla.analysis.DefinitionCollector;


import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.Start;

/**
 * This class eliminates all definition calls in the MACHINE.
 * A definition call will be replaced by the right-hand side of the definition 
 * and all parameter on the RHS are replaced by the arguments of the call.
 * 
 * Note: All parameters of a definition are replaced before calls of sub-definitions are resolved.
 * This behavior is similar to what ProB does by eliminating of all definitions.
 * 
 * 
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 *
 */
public class DefinitionsEliminator extends DepthFirstAdapter{
	
	private Hashtable<String, PDefinition> definitionsTable;
	private ArrayList<Hashtable<String, PExpression>> contextStack;
	
	
	public DefinitionsEliminator(Start node){
		DefinitionCollector collector = new DefinitionCollector(node);
		definitionsTable = collector.getDefinitions();
		contextStack = new ArrayList<Hashtable<String,PExpression>>();
		
	}
	
	
    @Override
    public void caseADefinitionExpression(ADefinitionExpression node)
    {

    	String name = node.getDefLiteral().getText();
    	PDefinition def = definitionsTable.get(name);
    	
    	AExpressionDefinitionDefinition t = (AExpressionDefinitionDefinition) def.clone();
    	
    	Hashtable<String, PExpression> context = new Hashtable<String, PExpression>();
    	ArrayList<PExpression> arguments = new ArrayList<PExpression>(node.getParameters());
    	for (int i = 0; i < t.getParameters().size(); i++) {
    		AIdentifierExpression p = (AIdentifierExpression) t.getParameters().get(i);
    		context.put(p.toString(), arguments.get(i));
		}
    	contextStack.add(context);
    	
    	t.apply(this);

    	node.replaceBy(t.getRhs());
    }
	
    @Override
    public void caseADefinitionPredicate(ADefinitionPredicate node)
    {
    	String name = node.getDefLiteral().getText();
    	PDefinition def = definitionsTable.get(name);
    	APredicateDefinitionDefinition t = (APredicateDefinitionDefinition) def.clone();
    	
    	Hashtable<String, PExpression> context = new Hashtable<String, PExpression>();
    	ArrayList<PExpression> arguments = new ArrayList<PExpression>(node.getParameters());
    	for (int i = 0; i < t.getParameters().size(); i++) {
    		AIdentifierExpression p = (AIdentifierExpression) t.getParameters().get(i);
    		context.put(p.toString(), arguments.get(i));
		}
    	contextStack.add(context);
    	
    	t.apply(this);

    	node.replaceBy(t.getRhs());
    }
    
    
    
    
    @Override
    public void caseAIdentifierExpression(AIdentifierExpression node)
    {
    	if(contextStack.size() == 0)
    		return;
    	
    	Hashtable<String, PExpression> context = contextStack.get(contextStack.size()-1);
    	PExpression e = context.get(node.toString());
    	if(e != null){
    		node.replaceBy(e);
    	}
    }
    
	
}




