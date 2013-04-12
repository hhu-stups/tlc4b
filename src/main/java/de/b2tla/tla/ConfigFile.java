package de.b2tla.tla;

import java.util.ArrayList;

import de.b2tla.tla.config.ConfigFileAssignment;


public class ConfigFile {

	private final ArrayList<ConfigFileAssignment> assignments;
	private boolean invariant;
	private boolean init;
	private boolean next;
	private int assertionsSize;
	private boolean goal;
	
	
	public ConfigFile(){
		this.assignments = new ArrayList<ConfigFileAssignment>();
		this.invariant = false;
	}


	public ArrayList<ConfigFileAssignment> getAssignments() {
		return assignments;
	}


	public boolean isInvariant() {
		return invariant;
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


	public void setInvariant() {
		this.invariant = true;
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
	
	
	public void setGoal(){
		this.goal = true;
	}
	
	public boolean isGoal(){
		return this.goal;
	}
	
}
