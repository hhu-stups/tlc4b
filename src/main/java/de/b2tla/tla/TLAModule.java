package de.b2tla.tla;

import java.util.ArrayList;
import java.util.LinkedList;

import de.b2tla.analysis.DefinitionsOrder;
import de.b2tla.analysis.MachineContext;
import de.b2tla.analysis.PrimedNodesMarker;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PDefinition;
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
	private ArrayList<PDefinition> bDefinitions;
	private final ArrayList<Node> assertions;
	
	private ArrayList<PDefinition> allDefinitions;

	public TLAModule() {
		this.definitions = new ArrayList<TLADefinition>();
		this.constants = new ArrayList<Node>();
		this.assumes = new ArrayList<Node>();
		this.variables = new ArrayList<Node>();
		this.initPredicates = new ArrayList<Node>();
		this.operations = new ArrayList<POperation>();
		this.bDefinitions = new ArrayList<PDefinition>();
		this.assertions = new ArrayList<Node>();
		
		this.allDefinitions = new ArrayList<PDefinition>();
	}

	public void sortAllDefinitions(MachineContext machineContext){
		DefinitionsOrder defOrder = new DefinitionsOrder(machineContext, this.allDefinitions);
		this.allDefinitions = defOrder.getAllDefinitions();
	}
	
	public void addToAllDefinitions(PDefinition def){
		this.allDefinitions.add(def);
	}
	
	public ArrayList<PDefinition> getAllDefinitions(){
		return allDefinitions;
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

	public void setBDefinitions(ArrayList<PDefinition> defs){
		this.bDefinitions = defs;
	}
	
	public ArrayList<PDefinition> getBDefinitions() {
		return bDefinitions;
	}

}
