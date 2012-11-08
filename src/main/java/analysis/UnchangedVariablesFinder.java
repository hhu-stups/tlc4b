package analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceOrSubstitution;
import de.be4.classicalb.core.parser.node.AChoiceSubstitution;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AParallelSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.Start;
import exceptions.SubstitutionException;

/**
 * 
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 * 
 */
public class UnchangedVariablesFinder {
	private final Hashtable<Node, HashSet<Node>> unchangedVariablesTable;

	public Hashtable<Node, HashSet<Node>> getUnchangedVariablesTable() {
		return unchangedVariablesTable;
	}

	public UnchangedVariablesFinder(MachineContext c) {
		Start start = c.getTree();

		AssignedVariablesFinder aVF = new AssignedVariablesFinder(c);
		start.apply(aVF);
		// assignedVariablesTable = aVF.getAssignedVariablesTable();
		MissingVariablesFinder mVF = new MissingVariablesFinder(c,
				aVF.getAssignedVariablesTable());
		start.apply(mVF);
		this.unchangedVariablesTable = mVF.getMissingVariablesTable();
	}
}

/**
 * 
 * This class is a tree walker which searches for all assigned variables in a
 * branch of a operation body. The algorithm works in a bottom up style. The
 * {@link assignedVariablesTable} will finally contain all assigned variables
 * for a node. For example a {@link AParallelSubstitution} node will get a list
 * of all assigned variables of its children. Operation output parameter are
 * handled as variables.
 * 
 */

class AssignedVariablesFinder extends DepthFirstAdapter {
	private final Hashtable<Node, HashSet<Node>> assignedVariablesTable;
	private final MachineContext machineContext;

	public AssignedVariablesFinder(MachineContext machineContext) {
		this.assignedVariablesTable = new Hashtable<Node, HashSet<Node>>();
		this.machineContext = machineContext;
	}

	public Hashtable<Node, HashSet<Node>> getAssignedVariablesTable() {
		return assignedVariablesTable;
	}

	private HashSet<Node> getVariableList(Node node) {
		return assignedVariablesTable.get(node);
	}

	@Override
	public void caseAOperation(AOperation node) {
		node.getOperationBody().apply(this);
		assignedVariablesTable.put(node,
				getVariableList(node.getOperationBody()));
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		node.getSubstitutions().apply(this);
		assignedVariablesTable.put(node,
				getVariableList(node.getSubstitutions()));

		/*
		 * In the INITIALISATION clause all variables must be assigned .
		 */
		HashSet<Node> allVariables = new HashSet<Node>(machineContext
				.getVariables().values());
		HashSet<Node> foundVariables = new HashSet<Node>(
				getVariableList(node.getSubstitutions()));

		if (allVariables.retainAll(foundVariables)) {
			HashSet<Node> missingVariables = new HashSet<Node>(machineContext
					.getVariables().values());
			missingVariables.removeAll(allVariables);
			throw new SubstitutionException(
					"Missing assignment for variable(s): " + missingVariables);
		}

	}

	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		HashSet<Node> list = new HashSet<Node>();
		for (PExpression e : copy) {
			if (e instanceof AIdentifierExpression) {
				Node identifier = machineContext.getReferences().get(e);
				list.add(identifier);
			}
		}
		assignedVariablesTable.put(node, list);
	}

	@Override
	public void caseAChoiceSubstitution(AChoiceSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		HashSet<Node> list = new HashSet<Node>();
		for (PSubstitution e : copy) {
			e.apply(this);
			list.addAll(getVariableList(e));
		}
		assignedVariablesTable.put(node, list);
	}

	@Override
	public void caseAChoiceOrSubstitution(AChoiceOrSubstitution node) {
		node.getSubstitution().apply(this);
		assignedVariablesTable.put(node,
				getVariableList(node.getSubstitution()));
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		HashSet<Node> list = new HashSet<Node>();
		node.getThen().apply(this);
		list.addAll(getVariableList(node.getThen()));

		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
			list.addAll(getVariableList(e));
		}
		node.getElse().apply(this);
		list.addAll(getVariableList(node.getElse()));
		assignedVariablesTable.put(node, list);
	}

	@Override
	public void caseAParallelSubstitution(AParallelSubstitution node) {
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		HashSet<Node> list = new HashSet<Node>();
		for (PSubstitution e : copy) {
			HashSet<Node> listOfe = getVariableList(e);
			HashSet<Node> temp = new HashSet<Node>(list);
			temp.retainAll(listOfe);
			if (temp.size() > 0) {
				throw new SubstitutionException("The variable(s) " + temp
						+ " are assigned twice");
			}
			list.addAll(listOfe);
		}
		// System.out.println(list);
		assignedVariablesTable.put(node, list);
	}

}

/**
 * This class is a tree walker which calculates all missing variables
 * assignments for each node inside a operation body. Missing variables
 * assignments correspond to unchanged variables in TLA+.
 * 
 * 
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 * 
 */

class MissingVariablesFinder extends DepthFirstAdapter {
	private final MachineContext machineContext;
	private final Hashtable<Node, HashSet<Node>> assignedIdentifiersTable;

	private final Hashtable<Node, HashSet<Node>> expectedVariablesTable;
	private final Hashtable<Node, HashSet<Node>> expectedOutputParametersTable;

	private final Hashtable<Node, HashSet<Node>> missingVariablesTable;

	public Hashtable<Node, HashSet<Node>> getMissingVariablesTable() {
		return missingVariablesTable;
	}

	public MissingVariablesFinder(MachineContext c,
			Hashtable<Node, HashSet<Node>> assignedVariablesTable) {
		this.machineContext = c;
		this.assignedIdentifiersTable = assignedVariablesTable;

		this.expectedVariablesTable = new Hashtable<Node, HashSet<Node>>();
		this.expectedOutputParametersTable = new Hashtable<Node, HashSet<Node>>();

		this.missingVariablesTable = new Hashtable<Node, HashSet<Node>>();
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		// do nothing
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

		missingVariablesTable.put(node, missingVariablesTable.get(body));
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

	private void check(Node node) {
		HashSet<Node> found = assignedIdentifiersTable.get(node);

		HashSet<Node> missingVariables = new HashSet<Node>(
				expectedVariablesTable.get(node));
		missingVariables.removeAll(found);
		missingVariablesTable.put(node, missingVariables);

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

		missingVariablesTable.put(node, missingVariablesTable.get(sub));

	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		check(node);

		// Separating variables and output parameters
		HashSet<Node> foundIdentifiers = assignedIdentifiersTable.get(node);
		HashSet<Node> variables = new HashSet<Node>(foundIdentifiers);
		variables.removeAll(expectedOutputParametersTable.get(node));

		
		expectedOutputParametersTable.put(node.getThen(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getThen(), variables);
		node.getThen().apply(this);
		
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			expectedOutputParametersTable.put(e,
					expectedOutputParametersTable.get(node));
			expectedVariablesTable.put(e, variables);
			e.apply(this);
		}
		
		expectedOutputParametersTable.put(node.getElse(),
				expectedOutputParametersTable.get(node));
		expectedVariablesTable.put(node.getElse(), variables);
		node.getElse().apply(this);
	}

}
