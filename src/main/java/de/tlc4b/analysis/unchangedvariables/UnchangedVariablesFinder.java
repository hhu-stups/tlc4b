package de.tlc4b.analysis.unchangedvariables;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AAssertionSubstitution;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesElementOfSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.ABlockSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceOrSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceSubstitution;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.AIfElsifSubstitution;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.ALetSubstitution;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AParallelSubstitution;
import de.be4.classicalb.core.parser.node.APreconditionSubstitution;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASelectWhenSubstitution;
import de.be4.classicalb.core.parser.node.ASkipSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.tlc4b.analysis.MachineContext;
import de.tlc4b.exceptions.SubstitutionException;

/**
 * This class is a tree walker which calculates all missing variables
 * assignments for each node inside a operation body. Missing variables
 * assignments correspond to unchanged variables in TLA+. B definitions or the
 * initialisation are not visited by this class.
 */

public class UnchangedVariablesFinder extends DepthFirstAdapter {
	private final MachineContext machineContext;
	private final Hashtable<Node, HashSet<Node>> assignedIdentifiersTable;

	// this table contains a set of all variables which must be assigned in the
	// node or in the sub nodes of the node
	private final Hashtable<Node, HashSet<Node>> expectedVariablesTable;
	private final Hashtable<Node, HashSet<Node>> expectedOutputParametersTable;

	private final Hashtable<Node, HashSet<Node>> unchangedVariablesTable;

	private final Hashtable<Node, HashSet<Node>> unchangedVariablesNull;

	public HashSet<Node> getUnchangedVariables(Node node) {
		return unchangedVariablesTable.get(node);
	}
	
	public HashSet<Node> getAssignedVariables(Node node){
		return assignedIdentifiersTable.get(node);
	}
	
	public boolean hasUnchangedVariables(Node node){
		HashSet<Node> set = unchangedVariablesTable.get(node);
		if(set== null){
			return false;
		}else{
			if(set.size() == 0){
				return false;
			}else
				return true;
		}
	}

	public HashSet<Node> getUnchangedVariablesNull(Node node) {
		return unchangedVariablesNull.get(node);
	}

	public UnchangedVariablesFinder(MachineContext c) {
		this.machineContext = c;

		AssignedVariablesFinder aVF = new AssignedVariablesFinder(c);
		this.assignedIdentifiersTable = aVF.getAssignedVariablesTable();

		this.expectedVariablesTable = new Hashtable<Node, HashSet<Node>>();
		this.expectedOutputParametersTable = new Hashtable<Node, HashSet<Node>>();

		this.unchangedVariablesTable = new Hashtable<Node, HashSet<Node>>();
		this.unchangedVariablesNull = new Hashtable<Node, HashSet<Node>>();

		c.getStartNode().apply(this);
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
	}

	@Override
	public void caseADefinitionsMachineClause(ADefinitionsMachineClause node) {
	}

	@Override
	public void caseAOperation(AOperation node) {
		HashSet<Node> expectedOutputParameter = new HashSet<Node>();
		List<PExpression> returnValues = new ArrayList<PExpression>(
				node.getReturnValues());
		for (PExpression e : returnValues) {
			expectedOutputParameter.add(e);
		}

		Node body = node.getOperationBody();
		expectedOutputParametersTable.put(body, expectedOutputParameter);
		expectedVariablesTable.put(body, new HashSet<Node>(machineContext
				.getVariables().values()));

		body.apply(this);

		// missingVariablesTable.put(node, missingVariablesTable.get(body));
	}

	private void check(Node node) {
		HashSet<Node> found = assignedIdentifiersTable.get(node);
		HashSet<Node> missingVariables = new HashSet<Node>(
				expectedVariablesTable.get(node));
		missingVariables.removeAll(found);
		unchangedVariablesTable.put(node, missingVariables);

		HashSet<Node> missingOutputParameter = new HashSet<Node>(
				expectedOutputParametersTable.get(node));
		missingOutputParameter.removeAll(found);
		if (missingOutputParameter.size() > 0) {
			throw new SubstitutionException(
					"To the following output parameters no values are assigned: "
							+ missingOutputParameter);
		}
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		check(node);
	}

	@Override
	public void caseABecomesSuchSubstitution(ABecomesSuchSubstitution node) {
		check(node);
	}

	@Override
	public void caseABecomesElementOfSubstitution(
			ABecomesElementOfSubstitution node) {
		check(node);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		check(node);

		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		for (PSubstitution e : copy) {

			expectedOutputParametersTable.put(e, new HashSet<Node>());
			expectedVariablesTable.put(e, new HashSet<Node>());
			e.apply(this);
		}
	}

	@Override
	public void caseAAnySubstitution(AAnySubstitution node) {
		check(node);

		expectedOutputParametersTable.put(node.getThen(), new HashSet<Node>());
		expectedVariablesTable.put(node.getThen(), new HashSet<Node>());
		node.getThen().apply(this);
	}

	@Override
	public void caseALetSubstitution(ALetSubstitution node) {
		check(node);

		expectedOutputParametersTable.put(node.getSubstitution(),
				new HashSet<Node>());
		expectedVariablesTable.put(node.getSubstitution(), new HashSet<Node>());
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		check(node);

		// Separating variables and output parameters
		HashSet<Node> foundIdentifiers = assignedIdentifiersTable.get(node);
		HashSet<Node> variables = new HashSet<Node>(foundIdentifiers);
		variables.removeAll(expectedOutputParametersTable.get(node));

		// System.out.println(parameters);

		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		for (PSubstitution e : copy) {
			// each child of CHOICE must assign all variables and all output
			// parameter
			expectedOutputParametersTable.put(e,
					expectedOutputParametersTable.get(node));
			expectedVariablesTable.put(e, variables);
			e.apply(this);
		}
	}

	@Override
	public void caseAChoiceOrSubstitution(AChoiceOrSubstitution node) {
		Node sub = node.getSubstitution();
		expectedOutputParametersTable.put(sub,
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(sub, expectedVariablesTable.get(node));

		sub.apply(this);

		unchangedVariablesTable.put(node, unchangedVariablesTable.get(sub));

	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		check(node);
		// Separating variables and output parameters
		HashSet<Node> foundIdentifiers = assignedIdentifiersTable.get(node);
		HashSet<Node> foundVariables = new HashSet<Node>(foundIdentifiers);
		foundVariables.removeAll(expectedOutputParametersTable.get(node));

		expectedOutputParametersTable.put(node.getThen(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getThen(), foundVariables);
		node.getThen().apply(this);

		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			expectedOutputParametersTable.put(e,
					expectedOutputParametersTable.get(node));
			expectedVariablesTable.put(e, foundVariables);
			e.apply(this);
		}

		if (node.getElse() != null) {
			expectedOutputParametersTable.put(node.getElse(),
					expectedOutputParametersTable.get(node));
			expectedVariablesTable.put(node.getElse(), foundVariables);
			node.getElse().apply(this);
		} else {
			unchangedVariablesNull.put(node,
					assignedIdentifiersTable.get(node.getThen()));
		}

	}

	@Override
	public void caseAIfElsifSubstitution(AIfElsifSubstitution node) {
		expectedOutputParametersTable.put(node.getThenSubstitution(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getThenSubstitution(),
				expectedVariablesTable.get(node));
		node.getThenSubstitution().apply(this);
	}

	@Override
	public void caseAPreconditionSubstitution(APreconditionSubstitution node) {
		// check(node);
		//
		// // Separating variables and output parameters
		// HashSet<Node> foundIdentifiers = assignedIdentifiersTable.get(node);
		// System.out.println(foundIdentifiers);
		// HashSet<Node> foundVariables = new HashSet<Node>(foundIdentifiers);
		// foundVariables.removeAll(expectedOutputParametersTable.get(node));

		expectedOutputParametersTable.put(node.getSubstitution(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getSubstitution(),
				expectedVariablesTable.get(node));
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseAAssertionSubstitution(AAssertionSubstitution node) {
		expectedOutputParametersTable.put(node.getSubstitution(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getSubstitution(),
				expectedVariablesTable.get(node));
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseABlockSubstitution(ABlockSubstitution node) {
		expectedOutputParametersTable.put(node.getSubstitution(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getSubstitution(),
				expectedVariablesTable.get(node));
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseASelectSubstitution(ASelectSubstitution node) {
		check(node);
		// Separating variables and output parameters
		HashSet<Node> foundIdentifiers = assignedIdentifiersTable.get(node);
		HashSet<Node> variables = new HashSet<Node>(foundIdentifiers);
		variables.removeAll(expectedOutputParametersTable.get(node));

		expectedOutputParametersTable.put(node.getThen(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getThen(), variables);
		node.getThen().apply(this);
		{
			List<PSubstitution> copy = new ArrayList<PSubstitution>(
					node.getWhenSubstitutions());
			for (PSubstitution e : copy) {
				expectedOutputParametersTable.put(e,
						expectedOutputParametersTable.get(node));
				expectedVariablesTable.put(e, variables);
				e.apply(this);
			}
		}

		if (node.getElse() != null) {
			expectedOutputParametersTable.put(node.getElse(),
					expectedOutputParametersTable.get(node));
			expectedVariablesTable.put(node.getElse(), variables);
			node.getElse().apply(this);
		}
	}

	@Override
	public void caseASelectWhenSubstitution(ASelectWhenSubstitution node) {
		check(node);
		expectedOutputParametersTable.put(node.getSubstitution(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getSubstitution(),
				expectedVariablesTable.get(node));
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseASkipSubstitution(ASkipSubstitution node) {
		check(node);
	}
}
