package b2tla.tla;

import java.util.ArrayList;

public class ConfigFile {

	protected final ArrayList<ConfigFileAssignment> assignments;
	protected boolean invariant;
	
	
	public ConfigFile(){
		this.assignments = new ArrayList<ConfigFileAssignment>();
		this.invariant = false;
	}
	
}
