package analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import btypes.AbstractHasFollowers;
import btypes.BType;
import btypes.BoolType;
import btypes.ITypechecker;
import btypes.IntegerOrSetOfPairType;
import btypes.IntegerOrSetType;
import btypes.IntegerType;
import btypes.ModelValueType;
import btypes.PairType;
import btypes.SequenceType;
import btypes.SetType;
import btypes.UntypedType;




import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABooleanFalseExpression;
import de.be4.classicalb.core.parser.node.ABooleanTrueExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.AEmptySetExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AMinusExpression;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.APreconditionSubstitution;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASequenceExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.AVariablesModelClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import exceptions.TypeErrorException;
import exceptions.UnificationException;

public class Typechecker extends DepthFirstAdapter implements ITypechecker {

	private final Hashtable<Node, BType> types;
	private final Hashtable<Node, Node> referenceTable;
	private final MachineContext context;

	public Typechecker(MachineContext machineContext,
			Hashtable<String, MachineContext> contextTable,
			Hashtable<String, Typechecker> typecheckerTable) {
		this.context = machineContext;
		this.types = new Hashtable<Node, BType>();
		this.referenceTable = machineContext.getReferences();
	}

	public Typechecker(MachineContext c) {
		this.types = new Hashtable<Node, BType>();
		this.referenceTable = c.getReferences();
		this.context = c;
		c.getTree().apply(this);
	}

	public Hashtable<Node, BType> getTypes() {
		return types;
	}

	public MachineContext getContext() {
		return context;
	}

	public void setType(Node node, BType t) {
		this.types.put(node, t);
		if (t instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) t).addFollower(node);
		}
	}

	public BType getType(Node node) {
		return types.get(node);
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		inAAbstractMachineParseUnit(node);
		if (node.getVariant() != null) {
			node.getVariant().apply(this);
		}
		if (node.getHeader() != null) {
			node.getHeader().apply(this);
		}
		{
			List<PMachineClause> copy = new ArrayList<PMachineClause>(
					node.getMachineClauses());
			PMachineClauseComparator comperator = new PMachineClauseComparator();
			// Sort the machine clauses
			Collections.sort(copy, comperator);
			for (PMachineClause e : copy) {
				e.apply(this);
			}
		}
		outAAbstractMachineParseUnit(node);
	}

	/**
	 * Declarations
	 */

	@Override
	public void caseAMachineHeader(AMachineHeader node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		for (PExpression e : copy) {
			AIdentifierExpression p = (AIdentifierExpression) e;
			String name = Utils.getIdentifierAsString(p.getIdentifier());

			String firstchar = name.substring(0, 1);
			String test = firstchar.toUpperCase();
			if (firstchar.equals(test)) {
				ModelValueType m = new ModelValueType(name);
				setType(p, m);
			} else {
				UntypedType u = new UntypedType();
				setType(p, u);
			}
		}
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression id = (AIdentifierExpression) e;
			UntypedType u = new UntypedType();
			setType(id, u);
		}
	}

	@Override
	public void caseAVariablesMachineClause(AVariablesMachineClause node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			UntypedType u = new UntypedType();
			setType(v, u);
		}
	}

	/**
	 * Properties
	 */

	@Override
	public void caseAConstraintsMachineClause(AConstraintsMachineClause node) {
		if (node.getPredicates() != null) {
			setType(node.getPredicates(), BoolType.getInstance());
			node.getPredicates().apply(this);
		}
		Hashtable<String, Node> parameter = context.getMachineParameters();
		for (String c : parameter.keySet()) {
			Node n = parameter.get(c);
			if (getType(n).isUntyped()) {
				throw new TypeErrorException(
						"Can not infer type of parameter '" + c + "'");
			}
		}
	}

	@Override
	public void caseAPropertiesMachineClause(final APropertiesMachineClause node) {
		if (node.getPredicates() != null) {
			setType(node.getPredicates(), BoolType.getInstance());
			node.getPredicates().apply(this);
		}
		Hashtable<String, Node> constants = context.getConstants();
		for (String c : constants.keySet()) {
			Node n = constants.get(c);
			if (getType(n).isUntyped()) {
				throw new TypeErrorException("Can not infer type of constant '"
						+ c + "'");
			}
		}
	}

	@Override
	public void caseAInvariantMachineClause(AInvariantMachineClause node) {
		if (node.getPredicates() != null) {
			setType(node.getPredicates(), BoolType.getInstance());
			node.getPredicates().apply(this);
		}
		Hashtable<String, Node> variables = context.getVariables();
		for (String c : variables.keySet()) {
			Node n = variables.get(c);
			if (getType(n).isUntyped()) {
				throw new TypeErrorException("Can not infer type of variable '"
						+ c + "'");
			}
		}
	}

	@Override
	public void caseAInitialisationMachineClause(
			AInitialisationMachineClause node) {
		if (node.getSubstitutions() != null) {
			node.getSubstitutions().apply(this);
		}
	}

	/**
	 * Expressions
	 */

	@Override
	public void caseAConjunctPredicate(AConjunctPredicate node) {
		inAConjunctPredicate(node);
		BoolType.getInstance().unify(getType(node), this);
		if (node.getLeft() != null) {
			setType(node.getLeft(), BoolType.getInstance());
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			setType(node.getRight(), BoolType.getInstance());
			node.getRight().apply(this);
		}
		outAConjunctPredicate(node);
	}

	@Override
	public void caseAEqualPredicate(AEqualPredicate node) {
		BoolType.getInstance().unify(getType(node), this);
		try {

		} catch (UnificationException e) {
			throw new TypeErrorException("Expected '" + getType(node)
					+ "', found BOOL at '=' \n" + node.getClass());
		}

		UntypedType x = new UntypedType();
		setType(node.getLeft(), x);
		setType(node.getRight(), x);

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
	}

	@Override
	public void caseAMemberPredicate(AMemberPredicate node) {
		inAMemberPredicate(node);

		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set.getSubtype());
		setType(node.getRight(), set);

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAMemberPredicate(node);
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {

		// System.out.println(node + " "+ getType(node));
		Node originalIdentifier = referenceTable.get(node);

		BType expected = getType(node);
		if (expected == null)
			throw new RuntimeException(); // TODO

		getType(node).unify(getType(originalIdentifier), this);

		{
			List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());
			for (TIdentifierLiteral e : copy) {
				e.apply(this);
			}
		}
	}

	/**
	 * Substitutions
	 * 
	 */

	@Override
	public void caseAPreconditionSubstitution(APreconditionSubstitution node) {
		setType(node.getPredicate(), BoolType.getInstance());
		node.getPredicate().apply(this);
		node.getSubstitution().apply(this);
	}

	@Override
	public void caseAIfSubstitution(AIfSubstitution node) {
		setType(node.getCondition(), BoolType.getInstance());
		node.getCondition().apply(this);
		node.getThen().apply(this);
		List<PSubstitution> copy = new ArrayList<PSubstitution>(
				node.getElsifSubstitutions());
		for (PSubstitution e : copy) {
			e.apply(this);
		}
		node.getElse().apply(this);
	}

	@Override
	public void caseAAssignSubstitution(AAssignSubstitution node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getLhsExpression());
		List<PExpression> copy2 = new ArrayList<PExpression>(
				node.getRhsExpressions());

		for (int i = 0; i < copy.size(); i++) {
			PExpression left = copy.get(i);
			PExpression right = copy2.get(i);

			UntypedType x = new UntypedType();
			setType(left, x);
			setType(right, x);
		}

		for (PExpression e : copy) {
			e.apply(this);
		}

		for (PExpression e : copy2) {
			e.apply(this);
		}
	}

	@Override
	public void caseAMultOrCartExpression(AMultOrCartExpression node) {
		inAMultOrCartExpression(node);
		BType expected = getType(node);

		if (expected instanceof UntypedType) {
			IntegerOrSetOfPairType t = new IntegerOrSetOfPairType();
			IntegerOrSetOfPairType res = (IntegerOrSetOfPairType) expected
					.unify(t, this);
			setType(node.getLeft(), res.getFirst());
			setType(node.getRight(), res.getSecond());
		} else if (expected instanceof IntegerType) {
			setType(node.getLeft(), IntegerType.getInstance());
			setType(node.getRight(), IntegerType.getInstance());
		} else if (expected instanceof SetType) {
			SetType set = new SetType(new PairType(new UntypedType(),
					new UntypedType()));
			SetType res = (SetType) expected.unify(set, this);
			PairType pair = (PairType) res.getSubtype();
			setType(node.getLeft(), new SetType(pair.getFirst()));
			setType(node.getRight(), new SetType(pair.getSecond()));
		} else if (expected instanceof IntegerOrSetOfPairType) {
			setType(node.getLeft(),
					((IntegerOrSetOfPairType) expected).getFirst());
			setType(node.getRight(),
					((IntegerOrSetOfPairType) expected).getSecond());

		} else if (expected instanceof IntegerOrSetType) {
			IntegerOrSetOfPairType t = new IntegerOrSetOfPairType();
			t = (IntegerOrSetOfPairType) t.unify(expected, this);
			setType(node.getLeft(), t.getFirst());
			setType(node.getRight(), t.getSecond());
		} else {
			throw new RuntimeException("Expected " + expected
					+ ", found Integer or Card");
		}
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAMultOrCartExpression(node);
	}

	@Override
	public void caseAIntegerExpression(AIntegerExpression node) {
		inAIntegerExpression(node);

		IntegerType.getInstance().unify(getType(node), this);

		if (node.getLiteral() != null) {
			node.getLiteral().apply(this);
		}
		outAIntegerExpression(node);
	}

	@Override
	public void caseASetExtensionExpression(ASetExtensionExpression node) {
		inASetExtensionExpression(node);
		SetType set = new SetType(new UntypedType()).unify(getType(node), this);
		for (PExpression e : node.getExpressions()) {
			setType(e, set.getSubtype());
		}

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getExpressions());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outASetExtensionExpression(node);
	}

	@Override
	public void caseABooleanTrueExpression(ABooleanTrueExpression node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in 'TRUE'");
		}
	}

	@Override
	public void caseABooleanFalseExpression(ABooleanFalseExpression node) {
		inABooleanFalseExpression(node);
		BoolType.getInstance().unify(getType(node), this);
		outABooleanFalseExpression(node);
	}

	@Override
	public void caseAAddExpression(AAddExpression node) {
		IntegerType.getInstance().unify(getType(node), this);
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		inAAddExpression(node);
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAAddExpression(node);
	}

	@Override
	public void caseAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		inAMinusOrSetSubtractExpression(node);
		BType expected = getType(node);

		if (expected instanceof IntegerType) {
			setType(node.getLeft(), IntegerType.getInstance());
			setType(node.getRight(), IntegerType.getInstance());
		} else if (expected instanceof UntypedType) {
			IntegerOrSetType t = new IntegerOrSetType();

			IntegerOrSetType res = (IntegerOrSetType) t.unify(expected, this);
			setType(node.getRight(), res);
			setType(node.getLeft(), res);
		} else if (expected instanceof IntegerOrSetOfPairType) {
			setType(node.getLeft(), expected);
			setType(node.getRight(), expected);
		}

		else {
			throw new RuntimeException();
		}

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAMinusOrSetSubtractExpression(node);
	}

	@Override
	public void caseASequenceExtensionExpression(
			ASequenceExtensionExpression node) {
		inASequenceExtensionExpression(node);
		BType expected = getType(node);

		SequenceType seq = (SequenceType) new SequenceType(new UntypedType())
				.unify(expected, this);
		for (PExpression e : node.getExpression()) {
			setType(e, seq.getSubtype());
		}

		{
			List<PExpression> copy = new ArrayList<PExpression>(
					node.getExpression());
			for (PExpression e : copy) {
				e.apply(this);
			}
		}
		outASequenceExtensionExpression(node);
	}

	@Override
	public void caseAEmptySetExpression(AEmptySetExpression node) {
		inAEmptySetExpression(node);
		getType(node).unify(new SetType(new UntypedType()), this);
		outAEmptySetExpression(node);
	}

	@Override
	public void caseAUnionExpression(AUnionExpression node) {
		inAUnionExpression(node);
		SetType set = new SetType(new UntypedType()).unify(getType(node), this);
		setType(node.getLeft(), set);
		setType(node.getRight(), set);

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outAUnionExpression(node);
	}

	@Override
	public void caseADisjunctPredicate(ADisjunctPredicate node) {
		inADisjunctPredicate(node);
		BoolType.getInstance().unify(getType(node), this);
		setType(node.getLeft(), BoolType.getInstance());
		setType(node.getRight(), BoolType.getInstance());
		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
		outADisjunctPredicate(node);
	}

}
