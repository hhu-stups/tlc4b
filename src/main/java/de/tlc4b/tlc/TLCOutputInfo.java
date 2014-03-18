package de.tlc4b.tlc;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;

import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Renamer;
import de.tlc4b.btypes.BType;
import de.tlc4b.tla.TLAModule;

public class TLCOutputInfo {
	
	Hashtable<String, String> namesMapping;
	Hashtable<String, BType> typesTable;
	Set<String> constants;
	boolean constantSetup= false;
	private boolean init= false;
	
	public boolean hasInitialisation(){
		return init;
	}
	
	public String getBName(String tlaName){
		return namesMapping.get(tlaName);
	}
	
	public BType getBType(String tlaName){
		return typesTable.get(tlaName);
	}
	
	public Hashtable<String, BType> getTypes(){
		return typesTable;
	}
	
	public void setConstantSetup(){
		this.constantSetup = true;
	}
	
	public boolean isAConstant(String tlaName){
		return constants.contains(getBName(tlaName));
	}
	
	public boolean hasConstants(){
		return constants.size()>0 || constantSetup;
	}
	
	public TLCOutputInfo(MachineContext machineContext, Renamer renamer,
			Hashtable<Node, BType> types, TLAModule tlaModule) {
		
		namesMapping = new Hashtable<String, String>();
		typesTable = new Hashtable<String, BType>();
		constants = machineContext.getConstants().keySet();
		init = tlaModule.getInitPredicates().size()>0;
		
		if(machineContext.getConstantsMachineClause() != null){
			this.constantSetup = true;
		}
		
		LinkedHashMap<String, Node> identifiers = new LinkedHashMap<String, Node>();
		identifiers.putAll(machineContext.getConstants());
		identifiers.putAll(machineContext.getVariables());
		identifiers.putAll(machineContext.getEnumValues());
		
		for (Iterator<String> iter = identifiers.keySet().iterator(); iter.hasNext();) {
			String name = iter.next();
			Node node = identifiers.get(name);
			String newName = renamer.getNameOfRef(node);
			namesMapping.put(newName, name);
			typesTable.put(newName, types.get(node));
		}
		
	}

}
