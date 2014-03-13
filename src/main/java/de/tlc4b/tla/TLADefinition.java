package de.tlc4b.tla;

import de.be4.classicalb.core.parser.node.Node;

public class TLADefinition {
	private Node name;
	private Node definition;
	private Integer intValue;
	
	public TLADefinition(Node name, Node definition){
		this.name = name;
		this.definition = definition;
	}
	
	public TLADefinition(Node con, Integer value) {
		this.name = con;
		this.intValue = value;
	}

	public Node getDefName(){
		return name;
	}
	public Node getDefinition(){
		return definition;
	}
	
	public Integer getInt(){
		return intValue;
	}
}

