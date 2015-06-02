package de.tlc4b.tlc;

import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.node.Node;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.analysis.Renamer;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.btypes.BType;
import de.tlc4b.tla.ConfigFile;
import de.tlc4b.tla.TLAModule;
import de.tlc4b.tla.config.ConfigFileAssignment;
import de.tlc4b.tla.config.ModelValueAssignment;

public class TLCOutputInfo {

	public Hashtable<String, String> namesMapping;
	Hashtable<String, BType> typesTable;
	Set<String> constants;
	boolean constantSetup = false;
	private boolean hasInit = false;

	public boolean hasInitialisation() {
		return hasInit;
	}

	public String getBName(String tlaName) {
		return namesMapping.get(tlaName);
	}

	public BType getBType(String tlaName) {
		return typesTable.get(tlaName);
	}

	public void setConstantSetup() {
		this.constantSetup = true;
	}

	public boolean isAConstant(String tlaName) {
		return constants.contains(getBName(tlaName));
	}

	public boolean hasConstants() {
		return constants.size() > 0 || constantSetup;
	}

	public TLCOutputInfo(MachineContext machineContext, Renamer renamer,
			Typechecker typechecker, TLAModule tlaModule, ConfigFile configFile) {

		this.namesMapping = new Hashtable<String, String>();
		this.typesTable = new Hashtable<String, BType>();
		this.constants = machineContext.getConstants().keySet();
		this.hasInit = tlaModule.getInitPredicates().size() > 0;

		if (machineContext.constantSetupInTraceFile()) {
			this.constantSetup = true;
		}

		LinkedHashMap<String, Node> identifiers = new LinkedHashMap<String, Node>();
		identifiers.putAll(machineContext.getConstants());
		identifiers.putAll(machineContext.getVariables());
		identifiers.putAll(machineContext.getEnumValues());
		//TODO add sets of modelvalues
		
		
		for (Entry<String, Node> entry : identifiers.entrySet()) {
			String name = entry.getKey();
			Node node = entry.getValue();
			String newName = renamer.getNameOfRef(node);
			namesMapping.put(newName, name);
			typesTable.put(newName, typechecker.getType(node));
		}
	}

}
