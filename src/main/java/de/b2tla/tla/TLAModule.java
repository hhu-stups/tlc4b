package de.b2tla.tla;

import java.util.ArrayList;
import java.util.LinkedList;

import de.b2tla.analysis.PrimedNodesMarker;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;

public class TLAModule {

	protected String moduleName;

	protected final ArrayList<TLADefinition> definitions;
	protected final ArrayList<Node> constants;
	private final ArrayList<Node> assumes;
	protected final ArrayList<Node> variables;
	protected PPredicate invariant;
	private final ArrayList<Node> initPredicates;
	protected final ArrayList<POperation> operations;
	private final ArrayList<Node> bDefinitions;
	private final ArrayList<Node> assertions;

	public TLAModule() {
		this.definitions = new ArrayList<TLADefinition>();
		this.constants = new ArrayList<Node>();
		this.assumes = new ArrayList<Node>();
		this.variables = new ArrayList<Node>();
		this.initPredicates = new ArrayList<Node>();
		this.operations = new ArrayList<POperation>();
		this.bDefinitions = new ArrayList<Node>();
		this.assertions = new ArrayList<Node>();
	}

	public ArrayList<Node> getAssertions(){
		return assertions;
	}
	
	public void addAssertion(Node node){
		assertions.add(node);
	}
	
	public void addAssume(Node node) {
		if (!assumes.contains(node))
			assumes.add(node);
	}

	public void addInit(Node node){
		if(!initPredicates.contains(node))
			initPredicates.add(node);
	}
	
	public boolean isInitPredicate(Node node){
		return initPredicates.contains(node);
	}
	
	public String getModuleName() {
		return moduleName;
	}

	public ArrayList<TLADefinition> getDefinitions() {
		return definitions;
	}

	public ArrayList<Node> getConstants() {
		return constants;
	}

	public ArrayList<Node> getAssume() {
		return assumes;
	}

	public ArrayList<Node> getVariables() {
		return variables;
	}

	public ArrayList<Node> getInitPredicates() {
		return initPredicates;
	}

	public ArrayList<POperation> getOperations() {
		return operations;
	}

	public PPredicate getInvariant() {
		return invariant;
	}

	public void addBDefinitions(Node def) {
		this.bDefinitions.add(def);
	}

	public ArrayList<Node> getBDefinitions() {
		return bDefinitions;
	}

}
