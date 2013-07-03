package de.b2tla.analysis;

import java.util.HashSet;
import java.util.Hashtable;


import de.be4.classicalb.core.parser.node.Node;

/**
 * 
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 * 
 */
public class UnchangedVariablesFinder {
	private final Hashtable<Node, HashSet<Node>> unchangedVariablesTable;
	private final Hashtable<Node, HashSet<Node>> unchangedVariablesNull;
	
	public Hashtable<Node, HashSet<Node>> getUnchangedVariablesTable() {
		return unchangedVariablesTable;
	}
	
	public Hashtable<Node, HashSet<Node>> getUnchangedVariablesNull() {
		return unchangedVariablesNull;
	}

	public UnchangedVariablesFinder(MachineContext c) {
//		Start start = c.getTree();

		AssignedVariablesFinder aVF = new AssignedVariablesFinder(c);
		//start.apply(aVF);
		// assignedVariablesTable = aVF.getAssignedVariablesTable();
		MissingVariablesFinder mVF = new MissingVariablesFinder(c,
				aVF.getAssignedVariablesTable());
		//start.apply(mVF);
		this.unchangedVariablesTable = mVF.getMissingVariablesTable();
		this.unchangedVariablesNull = mVF.getMissingVariablesNull();
	}
}