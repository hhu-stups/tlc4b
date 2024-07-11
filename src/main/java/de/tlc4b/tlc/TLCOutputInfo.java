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

public class TLCOutputInfo {

	public Hashtable<String, String> namesMapping;
	Hashtable<String, BType> typesTable;
	Set<String> constants;
	boolean constantSetup = false;
	private final boolean hasInit;

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
		return !constants.isEmpty() || constantSetup;
	}

	public TLCOutputInfo(MachineContext machineContext, Renamer renamer,
			Typechecker typechecker, TLAModule tlaModule, ConfigFile configFile) {

		this.namesMapping = new Hashtable<>();
		this.typesTable = new Hashtable<>();
		this.constants = machineContext.getConstants().keySet();
		this.hasInit = !tlaModule.getInitPredicates().isEmpty();

		if (machineContext.hasConstants()) {
			this.constantSetup = true;
		}

		LinkedHashMap<String, Node> identifiers = new LinkedHashMap<>();
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
