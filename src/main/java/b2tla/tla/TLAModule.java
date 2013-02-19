package b2tla.tla;

import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PPredicate;

public class TLAModule {

	
	protected String moduleName;
	
	protected final ArrayList<TLADefinition> definitions;
	protected final ArrayList<Node> constants;
	protected final ArrayList<Node> assumes;
	protected final ArrayList<Node> variables;
	protected PPredicate invariant;
	protected final ArrayList<Node> initPredicates;
	protected final ArrayList<Node> operations;

	public TLAModule(){
		this.definitions = new ArrayList<TLADefinition>();
		this.constants = new ArrayList<Node>();
		this.assumes = new ArrayList<Node>();
		this.variables = new ArrayList<Node>();
		this.initPredicates = new ArrayList<Node>();
		this.operations = new ArrayList<Node>();
	}

	public String getModuleName(){
		return moduleName;
	}
	
	public ArrayList<TLADefinition> getDefinitions(){
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

	public ArrayList<Node> getOperations() {
		return operations;
	}
	
	public PPredicate getInvariant() {
		return invariant;
	}
	
	
}
