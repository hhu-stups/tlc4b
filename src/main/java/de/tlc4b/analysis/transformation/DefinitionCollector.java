package de.tlc4b.analysis.transformation;

import java.util.Hashtable;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.ALocalOperationsMachineClause;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.Start;

/**
 * This class only collects all Definitions of a Machine. Definitions of other files which are included are not contained.
 *  
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 *
 */


public class DefinitionCollector extends DepthFirstAdapter {

	private Hashtable<String, PDefinition> definitionsTable;

	public Hashtable<String, PDefinition> getDefinitions(){
		return new Hashtable<String, PDefinition>(definitionsTable);
	}
	
	public DefinitionCollector(Start tree) {
		definitionsTable = new Hashtable<String, PDefinition>();
		tree.apply(this);
	}


	@Override
	public void caseAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		definitionsTable.put(node.getName().getText().toString(), node);
	}

	@Override
	public void caseASubstitutionDefinitionDefinition(
			ASubstitutionDefinitionDefinition node) {
		definitionsTable.put(node.getName().getText().toString(), node);
	}

	@Override
	public void caseAExpressionDefinitionDefinition(
			AExpressionDefinitionDefinition node) {
		definitionsTable.put(node.getName().getText().toString(), node);
	}

	/***************************************************************************
	 * exclude large sections of a machine without machine references by doing
	 * nothing
	 */

	@Override
	public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
	}

	@Override
	public void caseAOperationsMachineClause(AOperationsMachineClause node) {
	}

	@Override
	public void caseAPropertiesMachineClause(APropertiesMachineClause node) {
	}


	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
	}

	@Override
	public void caseALocalOperationsMachineClause(
			ALocalOperationsMachineClause node) {
	}

}
