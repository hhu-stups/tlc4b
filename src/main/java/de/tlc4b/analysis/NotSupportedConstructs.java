package de.tlc4b.analysis;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACaseSubstitution;
import de.be4.classicalb.core.parser.node.AExtendsMachineClause;
import de.be4.classicalb.core.parser.node.AImportsMachineClause;
import de.be4.classicalb.core.parser.node.AIncludesMachineClause;
import de.be4.classicalb.core.parser.node.APromotesMachineClause;
import de.be4.classicalb.core.parser.node.ARefinesModelClause;
import de.be4.classicalb.core.parser.node.ASeesModelClause;
import de.be4.classicalb.core.parser.node.ASequenceSubstitution;
import de.be4.classicalb.core.parser.node.AUsesMachineClause;
import de.be4.classicalb.core.parser.node.AWhileSubstitution;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.exceptions.NotSupportedException;

public class NotSupportedConstructs extends DepthFirstAdapter {

	public NotSupportedConstructs(Start start) {
		start.apply(this);
	}

	public void inARefinesModelClause(ARefinesModelClause node) {
		throw new NotSupportedException(
				"Refines clause is currently not supported.");
	}

	public void inAUsesMachineClause(AUsesMachineClause node) {
		throw new NotSupportedException(
				"USES clause is currently not supported.");
	}

	public void inAPromotesMachineClause(APromotesMachineClause node) {
		throw new NotSupportedException(
				"Promotes clause is currently not supported.");
	}

	public void inASeesModelClause(ASeesModelClause node) {
		throw new NotSupportedException(
				"Sees clause is currently not supported.");
	}

	public void inAIncludesMachineClause(AIncludesMachineClause node) {
		throw new NotSupportedException(
				"INCLUDES clause is currently not supported.");
	}

	public void inAExtendsMachineClause(AExtendsMachineClause node) {
		throw new NotSupportedException(
				"EXTENDS clause is currently not supported.");
	}

	public void inAImportsMachineClause(AImportsMachineClause node) {
		throw new NotSupportedException(
				"IMPORTS clause is currently not supported.");
	}

	public void inAWhileSubstitution(AWhileSubstitution node) {
		throw new NotSupportedException(
				"While substitutions are currently not supported.");
	}

	public void inACaseSubstitution(ACaseSubstitution node) {
		throw new NotSupportedException(
				"Case substitutions are currently not supported.");
	}

	public void inASequenceSubstitution(ASequenceSubstitution node) {
		throw new NotSupportedException(
				"Sequence substitutions ';' are currently not supported.");
	}

}
