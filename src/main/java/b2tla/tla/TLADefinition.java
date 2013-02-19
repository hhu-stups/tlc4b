package b2tla.tla;

import de.be4.classicalb.core.parser.node.Node;

public class TLADefinition {
	private Node name;
	private Node definition;
	public TLADefinition(Node name, Node definition){
		this.name = name;
		this.definition = definition;
	}
	
	public Node getDefName(){
		return name;
	}
	public Node getDefinition(){
		return definition;
	}
}

