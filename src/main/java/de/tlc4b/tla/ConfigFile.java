package de.tlc4b.tla;

import java.util.ArrayList;

import de.tlc4b.tla.config.ConfigFileAssignment;


public class ConfigFile {

	private final ArrayList<ConfigFileAssignment> assignments;
	private int invariantNumber;
	private boolean spec;
	private boolean init;
	private boolean next;
	private int assertionsSize;
	private boolean goal;
	
	
	public ConfigFile(){
		this.assignments = new ArrayList<ConfigFileAssignment>();
		this.invariantNumber = 0;
	}


	public ArrayList<ConfigFileAssignment> getAssignments() {
		return assignments;
	}

	public boolean isSpec(){
		return spec;
	}
	

	public void setInvariantNumber(int number) {
		this.invariantNumber = number;
	}


	public boolean isInit() {
		return init;
	}


	public boolean isNext() {
		return next;
	}
	
	public void addAssignment(ConfigFileAssignment assignment){
		assignments.add(assignment);
	}


	public int getInvariantNumber() {
		return this.invariantNumber;
	}


	public void setInit() {
		this.init = true;
	}


	public void setNext() {
		this.next = true;
	}


	public void setAssertionSize(int size) {
		assertionsSize = size;
	}
	
	public int getAssertionSize(){
		return assertionsSize;
	}
	
	public void setSpec(){
		this.spec = true;
	}
	
	public void setGoal(){
		this.goal = true;
	}
	
	public boolean isGoal(){
		return this.goal;
	}
	
}
