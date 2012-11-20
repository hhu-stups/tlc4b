package analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Hashtable;
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
import de.be4.classicalb.core.parser.node.ABoolSetExpression;
import de.be4.classicalb.core.parser.node.ABooleanFalseExpression;
import de.be4.classicalb.core.parser.node.ABooleanTrueExpression;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AConstraintsMachineClause;
import de.be4.classicalb.core.parser.node.AConvertBoolExpression;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.AEmptySetExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AEquivalencePredicate;
import de.be4.classicalb.core.parser.node.AGreaterEqualPredicate;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AIfSubstitution;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AIntSetExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.ALessPredicate;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AMaxExpression;
import de.be4.classicalb.core.parser.node.AMaxIntExpression;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AMinExpression;
import de.be4.classicalb.core.parser.node.AMinIntExpression;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AModuloExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.ANat1SetExpression;
import de.be4.classicalb.core.parser.node.ANatSetExpression;
import de.be4.classicalb.core.parser.node.ANatural1SetExpression;
import de.be4.classicalb.core.parser.node.ANaturalSetExpression;
import de.be4.classicalb.core.parser.node.ANegationPredicate;
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APreconditionSubstitution;
import de.be4.classicalb.core.parser.node.APredecessorExpression;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASequenceExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASuccessorExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.PSubstitution;
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
	public void caseAEqualPredicate(AEqualPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Expected '" + getType(node)
					+ "', found BOOL at '=' \n" + node.getClass());
		}

		UntypedType x = new UntypedType();
		setType(node.getLeft(), x);
		setType(node.getRight(), x);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node originalIdentifier = referenceTable.get(node);

		BType expected = getType(node);
		if (expected == null)
			throw new RuntimeException(); // TODO

		getType(node).unify(getType(originalIdentifier), this);
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

	/****************************************************************************
	 * Arithmetic operators *
	 ****************************************************************************/

	@Override
	public void caseAIntegerExpression(AIntegerExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in '" + node.getLiteral().getText()
					+ "'");
		}
	}

	@Override
	public void caseAIntegerSetExpression(AIntegerSetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'INTEGER'");
		}
	}

	@Override
	public void caseANaturalSetExpression(ANaturalSetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'NATURAL'");
		}
	}

	@Override
	public void caseANatural1SetExpression(ANatural1SetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'NATURAL1'");
		}
	}

	@Override
	public void caseAIntSetExpression(AIntSetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'INT'");
		}
	}

	@Override
	public void caseANatSetExpression(ANatSetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'NAT'");
		}
	}

	@Override
	public void caseANat1SetExpression(ANat1SetExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' in 'NAT1'");
		}
	}

	@Override
	public void caseAIntervalExpression(AIntervalExpression node) {
		try {
			SetType found = new SetType(IntegerType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER)' at interval operator");
		}

		setType(node.getLeftBorder(), IntegerType.getInstance());
		setType(node.getRightBorder(), IntegerType.getInstance());
		node.getLeftBorder().apply(this);
		node.getRightBorder().apply(this);
	}

	@Override
	public void caseAMaxIntExpression(AMaxIntExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in 'MAXINT'");
		}
	}

	@Override
	public void caseAMinIntExpression(AMinIntExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in 'MININT'");
		}
	}

	@Override
	public void caseAGreaterPredicate(AGreaterPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' > '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseALessPredicate(ALessPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' < '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAGreaterEqualPredicate(AGreaterEqualPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' >= '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseALessEqualPredicate(ALessEqualPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' <= '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAMinExpression(AMinExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' min '");
		}
		setType(node.getExpression(), new SetType(IntegerType.getInstance()));
		node.getExpression().apply(this);
	}

	@Override
	public void caseAMaxExpression(AMaxExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' min '");
		}
		setType(node.getExpression(), new SetType(IntegerType.getInstance()));
		node.getExpression().apply(this);
	}

	@Override
	public void caseAAddExpression(AAddExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' + '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		BType expected = getType(node);

		if (expected instanceof IntegerType) {
			setType(node.getLeft(), IntegerType.getInstance());
			setType(node.getRight(), IntegerType.getInstance());
		} else if (expected instanceof UntypedType) {
			IntegerOrSetType t = new IntegerOrSetType();

			IntegerOrSetType res = (IntegerOrSetType) t.unify(expected, this);
			setType(node.getRight(), res);
			setType(node.getLeft(), res);
		} else if (expected instanceof SetType) {
			setType(node.getLeft(), expected);
			setType(node.getRight(), expected);
		} else if (expected instanceof IntegerOrSetOfPairType) {
			setType(node.getLeft(), expected);
			setType(node.getRight(), expected);
		} else {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(_A)' or 'INTEGER' in ' - '");
		}

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
	}

	@Override
	public void caseAMultOrCartExpression(AMultOrCartExpression node) {
		BType expected = getType(node);

		if (expected instanceof UntypedType) {
			IntegerOrSetOfPairType t = new IntegerOrSetOfPairType();
			IntegerOrSetOfPairType res = (IntegerOrSetOfPairType) expected
					.unify(t, this);
			setType(node, res);
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
			setType(node, t);
			setType(node.getLeft(), t.getFirst());
			setType(node.getRight(), t.getSecond());
		} else {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(_A*_B)' or 'INTEGER' in ' * '");
		}

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseADivExpression(ADivExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' / '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAPowerOfExpression(APowerOfExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' ** '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAModuloExpression(AModuloExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in ' mod '");
		}
		setType(node.getLeft(), IntegerType.getInstance());
		setType(node.getRight(), IntegerType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseASuccessorExpression(ASuccessorExpression node) {
		SetType found = new SetType(new PairType(IntegerType.getInstance(),
				IntegerType.getInstance()));
		try {
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER*INTEGER)' in ' succ '");
		}
	}

	@Override
	public void caseAPredecessorExpression(APredecessorExpression node) {
		SetType found = new SetType(new PairType(IntegerType.getInstance(),
				IntegerType.getInstance()));
		try {
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(INTEGER*INTEGER)' in ' pred '");
		}
	}

	/**
	 * Booleans
	 */

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
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in 'FALSE'");
		}
	}

	@Override
	public void caseABoolSetExpression(ABoolSetExpression node) {
		try {
			SetType found = new SetType(BoolType.getInstance());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(BOOL)' in 'BOOL'");
		}
	}

	@Override
	public void caseAConvertBoolExpression(AConvertBoolExpression node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in 'bool(...)'");
		}
		setType(node.getPredicate(), BoolType.getInstance());
		node.getPredicate().apply(this);
	}

	/**
	 * Logical Operator
	 */

	@Override
	public void caseAConjunctPredicate(AConjunctPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' & '");
		}
		setType(node.getLeft(), BoolType.getInstance());
		setType(node.getRight(), BoolType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseADisjunctPredicate(ADisjunctPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' or '");
		}
		setType(node.getLeft(), BoolType.getInstance());
		setType(node.getRight(), BoolType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAImplicationPredicate(AImplicationPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' => '");
		}
		setType(node.getLeft(), BoolType.getInstance());
		setType(node.getRight(), BoolType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAEquivalencePredicate(AEquivalencePredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' <=> '");
		}
		setType(node.getLeft(), BoolType.getInstance());
		setType(node.getRight(), BoolType.getInstance());
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseANegationPredicate(ANegationPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'BOOL' in ' not '");
		}
		setType(node.getPredicate(), BoolType.getInstance());
		node.getPredicate().apply(this);
	}

	/**
	 * Sets
	 */

	@Override
	public void caseAEmptySetExpression(AEmptySetExpression node) {
		try {
			SetType found = new SetType(new UntypedType());
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(_A)' in ' {} '");
		}
	}

	@Override
	public void caseASetExtensionExpression(ASetExtensionExpression node) {
		SetType set;
		try {
			set = new SetType(new UntypedType()).unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(_A)' in ' {...} '");
		}

		for (PExpression e : node.getExpressions()) {
			setType(e, set.getSubtype());
		}

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getExpressions());
		for (PExpression e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		ArrayList<BType> typesList = new ArrayList<BType>();
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			UntypedType u = new UntypedType();
			typesList.add(u);
			setType(v, u);
		}
		BType listType = makePair(typesList);
		SetType found = new SetType(listType);

		try {
			found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found " + found + "'");
		}

		setType(node.getPredicates(), BoolType.getInstance());
		node.getPredicates().apply(this);
	}

	public static BType makePair(ArrayList<BType> list) {
		if (list.size() == 1)
			return list.get(0);
		PairType p = new PairType(list.get(0), null);
		for (int i = 1; i < list.size(); i++) {
			p.setSecond(list.get(i));
			if (i < list.size() - 1) {
				p = new PairType(p, null);
			}
		}
		return p;
	}

	@Override
	public void caseAPowSubsetExpression(APowSubsetExpression node) {
		SetType found = new SetType(new SetType(new UntypedType()));
		try {
			found = found.unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'POW(POW(_A))' in 'POW'");
		}

		setType(node.getExpression(), found.getSubtype());
		node.getExpression().apply(this);
	}

	@Override
	public void caseAMemberPredicate(AMemberPredicate node) {
		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set.getSubtype());
		setType(node.getRight(), set);

		if (node.getLeft() != null) {
			node.getLeft().apply(this);
		}
		if (node.getRight() != null) {
			node.getRight().apply(this);
		}
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

}
