package b2tla.analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.List;

import b2tla.btypes.AbstractHasFollowers;
import b2tla.btypes.BType;
import b2tla.btypes.BoolType;
import b2tla.btypes.FunctionType;
import b2tla.btypes.ITypechecker;
import b2tla.btypes.IntegerOrSetOfPairType;
import b2tla.btypes.IntegerOrSetType;
import b2tla.btypes.IntegerType;
import b2tla.btypes.ModelValueType;
import b2tla.btypes.PairType;
import b2tla.btypes.SequenceType;
import b2tla.btypes.SetType;
import b2tla.btypes.StringType;
import b2tla.btypes.StructType;
import b2tla.btypes.UntypedType;
import b2tla.exceptions.TypeErrorException;
import b2tla.exceptions.UnificationException;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;

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

			if(Character.isUpperCase(name.charAt(0))){
				
				ModelValueType m = new ModelValueType(name);
				setType(p, new SetType(m));
			}else{
				UntypedType u = new UntypedType();
				setType(p, u);
			}
		}
	}

	@Override
	public void caseASetsMachineClause(ASetsMachineClause node) {
		List<PSet> copy = new ArrayList<PSet>(node.getSetDefinitions());
		for (PSet e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAEnumeratedSetSet(AEnumeratedSetSet node) {
		List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
				node.getIdentifier());
		
		String setName = Utils.getIdentifierAsString(copy);
		SetType setType = new SetType(new ModelValueType(setName));
		setType(node, setType);
		List<PExpression> copy2 = new ArrayList<PExpression>(node.getElements());
		for (PExpression e : copy2) {
			setType(e, setType.getSubtype());
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
		LinkedHashMap<String, Node> parameter = context.getScalarParameter();
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
		LinkedHashMap<String, Node> constants = context.getConstants();
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
		LinkedHashMap<String, Node> variables = context.getVariables();
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
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		Node originalIdentifier = referenceTable.get(node);

		BType expected = getType(node);
		if (expected == null)
			throw new RuntimeException();

		BType found = getType(originalIdentifier);
		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + found + "'");
		}

	}

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
	public void caseAForallPredicate(AForallPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Expected '" + getType(node)
					+ "', found BOOL at 'For All' \n");
		}

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			setType(v, new UntypedType());
		}

		setType(node.getImplication(), BoolType.getInstance());
		node.getImplication().apply(this);
	}

	@Override
	public void caseAExistsPredicate(AExistsPredicate node) {
		try {
			BoolType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Expected '" + getType(node)
					+ "', found BOOL at 'Exists' \n");
		}

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			setType(v, new UntypedType());
		}

		setType(node.getPredicate(), BoolType.getInstance());
		node.getPredicate().apply(this);
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
	public void caseAUnaryMinusExpression(AUnaryMinusExpression node) {
		try {
			IntegerType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found 'INTEGER' in '-'");
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

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		BType expected = getType(node);
		try {
			IntegerType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + "INTEGER" + "'");
		}

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			setType(v, new UntypedType());
		}

		setType(node.getPredicates(), BoolType.getInstance());
		node.getPredicates().apply(this);

		setType(node.getExpression(), IntegerType.getInstance());
		node.getExpression().apply(this);
	}

	@Override
	public void caseAGeneralProductExpression(AGeneralProductExpression node) {
		BType expected = getType(node);
		try {
			IntegerType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + "INTEGER" + "'");
		}

		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			setType(v, new UntypedType());
		}

		setType(node.getPredicates(), BoolType.getInstance());
		node.getPredicates().apply(this);

		setType(node.getExpression(), IntegerType.getInstance());
		node.getExpression().apply(this);
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
	public void caseAPow1SubsetExpression(APow1SubsetExpression node) {
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
	public void caseAUnionExpression(AUnionExpression node) {
		SetType found = new SetType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		setType(node.getLeft(), found);
		setType(node.getRight(), found);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAIntersectionExpression(AIntersectionExpression node) {
		SetType found = new SetType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		setType(node.getLeft(), found);
		setType(node.getRight(), found);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseACardExpression(ACardExpression node) {
		BType found = IntegerType.getInstance();
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		setType(node.getExpression(), new SetType(new UntypedType()));
		node.getExpression().apply(this);
	}

	@Override
	public void caseAMemberPredicate(AMemberPredicate node) {
		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set.getSubtype());
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseANotMemberPredicate(ANotMemberPredicate node) {
		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set.getSubtype());
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseASubsetPredicate(ASubsetPredicate node) {
		BType expected = getType(node);
		try {
			BoolType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found 'BOOL'");
		}

		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set);
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseASubsetStrictPredicate(ASubsetStrictPredicate node) {
		BType expected = getType(node);
		try {
			BoolType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found 'BOOL'");
		}

		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set);
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseANotSubsetPredicate(ANotSubsetPredicate node) {
		BType expected = getType(node);
		try {
			BoolType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found 'BOOL'");
		}

		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set);
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseANotSubsetStrictPredicate(ANotSubsetStrictPredicate node) {
		BType expected = getType(node);
		try {
			BoolType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found 'BOOL'");
		}

		SetType set = new SetType(new UntypedType());

		setType(node.getLeft(), set);
		setType(node.getRight(), set);

		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAGeneralUnionExpression(AGeneralUnionExpression node) {
		SetType set = new SetType(new SetType(new UntypedType()));
		setType(node.getExpression(), set);
		node.getExpression().apply(this);

		BType found = ((SetType) getType(node.getExpression())).getSubtype();
		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + found + "'");
		}
	}

	@Override
	public void caseAGeneralIntersectionExpression(
			AGeneralIntersectionExpression node) {
		SetType set = new SetType(new SetType(new UntypedType()));
		setType(node.getExpression(), set);
		node.getExpression().apply(this);

		BType found = ((SetType) getType(node.getExpression())).getSubtype();
		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + found + "'");
		}
	}

	/**
	 * Functions
	 */

	@Override
	public void caseALambdaExpression(ALambdaExpression node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (PExpression e : copy) {
			AIdentifierExpression v = (AIdentifierExpression) e;
			setType(v, new UntypedType());
		}

		setType(node.getPredicate(), BoolType.getInstance());
		node.getPredicate().apply(this);

		setType(node.getExpression(), new UntypedType());
		node.getExpression().apply(this);

		ArrayList<BType> typesList = new ArrayList<BType>();
		for (PExpression e : copy) {
			typesList.add(getType(e));
		}
		BType domain = makePair(typesList);
		BType range = getType(node.getExpression());

		BType found = new FunctionType(domain, range);
		// BType found = new SetType(new PairType(domain, range));

		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseAFunctionExpression(AFunctionExpression node) {
		FunctionType func = new FunctionType(new UntypedType(),
				new UntypedType());
		setType(node.getIdentifier(), func);
		node.getIdentifier().apply(this);

		BType id = getType(node.getIdentifier());
		BType domainFound;
		BType rangeFound;
		if (id instanceof FunctionType) {
			domainFound = ((FunctionType) id).getDomain();
			rangeFound = ((FunctionType) id).getRange();
		} else {
			PairType p = (PairType) ((SetType) id).getSubtype();
			domainFound = p.getFirst();
			rangeFound = p.getSecond();
		}

		BType expected = getType(node);
		try {
			rangeFound.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ rangeFound + "'");
		}

		ArrayList<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		for (PExpression e : copy) {
			setType(e, new UntypedType());
			e.apply(this);
		}

		ArrayList<BType> foundList = new ArrayList<BType>();
		for (PExpression e : copy) {
			foundList.add(getType(e));
		}
		try {
			domainFound.unify(makePair(foundList), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + domainFound
					+ "' , found " + makePair(foundList) + "'");
		}

	}

	@Override
	public void caseADomainExpression(ADomainExpression node) {
		FunctionType f = new FunctionType(new UntypedType(), new UntypedType());
		setType(node.getExpression(), f);
		node.getExpression().apply(this);

		BType b = getType(node.getExpression());
		BType domainFound;
		if (b instanceof FunctionType) {
			domainFound = new SetType(((FunctionType) b).getDomain());
		} else {
			PairType p = (PairType) ((SetType) b).getSubtype();
			domainFound = new SetType(p.getFirst());
		}
		BType expected = getType(node);
		try {
			domainFound.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + domainFound + "'");
		}
	}

	@Override
	public void caseARangeExpression(ARangeExpression node) {
		FunctionType f = new FunctionType(new UntypedType(), new UntypedType());
		setType(node.getExpression(), f);
		node.getExpression().apply(this);

		BType b = getType(node.getExpression());
		BType rangeFound;
		if (b instanceof FunctionType) {
			rangeFound = new SetType(((FunctionType) b).getRange());
		} else {
			PairType p = (PairType) ((SetType) b).getSubtype();
			rangeFound = new SetType(p.getSecond());
		}
		BType expected = getType(node);
		try {
			rangeFound.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected
					+ "' , found '" + rangeFound + "'");
		}
	}

	@Override
	public void caseATotalFunctionExpression(ATotalFunctionExpression node) {
		setType(node.getLeft(), new SetType(new UntypedType()));
		node.getLeft().apply(this);
		setType(node.getRight(), new SetType(new UntypedType()));
		node.getRight().apply(this);

		BType left = ((SetType) getType(node.getLeft())).getSubtype();
		BType right = ((SetType) getType(node.getRight())).getSubtype();

		BType found = new SetType(new FunctionType(left, right));
		BType expected = getType(node);
		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}

	}

	@Override
	public void caseAPartialFunctionExpression(APartialFunctionExpression node) {
		setType(node.getLeft(), new SetType(new UntypedType()));
		node.getLeft().apply(this);
		setType(node.getRight(), new SetType(new UntypedType()));
		node.getRight().apply(this);

		BType left = ((SetType) getType(node.getLeft())).getSubtype();
		BType right = ((SetType) getType(node.getRight())).getSubtype();

		BType found = new SetType(new SetType(new PairType(left, right)));
		BType expected = getType(node);
		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}

	}

	/**
	 * Relations
	 */

	@Override
	public void caseACoupleExpression(ACoupleExpression node) {
		BType expected = getType(node);

		List<PExpression> copy = new ArrayList<PExpression>(node.getList());

		ArrayList<BType> list = new ArrayList<BType>();

		for (PExpression e : copy) {
			setType(e, new UntypedType());
			e.apply(this);
			list.add(getType(e));
		}

		BType found = makePair(list);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseARelationsExpression(ARelationsExpression node) {
		setType(node.getLeft(), new SetType(new UntypedType()));
		node.getLeft().apply(this);
		setType(node.getRight(), new SetType(new UntypedType()));
		node.getRight().apply(this);

		BType left = ((SetType) getType(node.getLeft())).getSubtype();
		BType right = ((SetType) getType(node.getRight())).getSubtype();

		BType found = new SetType(new SetType(new PairType(left, right)));
		BType expected = getType(node);
		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseAIdentityExpression(AIdentityExpression node) {
		SetType s = new SetType(new UntypedType());
		setType(node.getExpression(), s);
		node.getExpression().apply(this);

		s = (SetType) getType(node.getExpression());

		BType found = new SetType(new PairType(s.getSubtype(), s.getSubtype()));
		BType expected = getType(node);

		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseADomainRestrictionExpression(
			ADomainRestrictionExpression node) {
		UntypedType u = new UntypedType();
		SetType left = new SetType(u);
		SetType right = new SetType(new PairType(u, new UntypedType()));
		setType(node.getLeft(), left);
		setType(node.getRight(), right);
		node.getLeft().apply(this);
		node.getRight().apply(this);

		BType found = getType(node.getRight());
		BType expected = getType(node);

		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseADomainSubtractionExpression(
			ADomainSubtractionExpression node) {
		UntypedType u = new UntypedType();
		SetType left = new SetType(u);
		SetType right = new SetType(new PairType(u, new UntypedType()));
		setType(node.getLeft(), left);
		setType(node.getRight(), right);
		node.getLeft().apply(this);
		node.getRight().apply(this);

		BType found = getType(node.getRight());
		BType expected = getType(node);

		try {
			expected.unify(found, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	/**
	 * Sequences
	 */

	@Override
	public void caseASequenceExtensionExpression(
			ASequenceExtensionExpression node) {
		BType expected = getType(node);
		BType found = new SequenceType(new UntypedType());
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		BType subtype;
		if (found instanceof SequenceType) {
			subtype = ((SequenceType) found).getSubtype();
		} else {
			PairType p = (PairType) ((SetType) found).getSubtype();
			subtype = p.getSecond();
		}
		for (PExpression e : node.getExpression()) {
			setType(e, subtype);
		}
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getExpression());
		for (PExpression e : copy) {
			e.apply(this);
		}
	}

	@Override
	public void caseAConcatExpression(AConcatExpression node) {
		BType found = new SequenceType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		setType(node.getLeft(), found);
		setType(node.getRight(), found);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseASizeExpression(ASizeExpression node) {
		BType expected = getType(node);
		try {
			IntegerType.getInstance().unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ IntegerType.getInstance() + "' in size(..)");
		}
		setType(node.getExpression(), new SequenceType(new UntypedType()));
		node.getExpression().apply(this);
	}

	@Override
	public void caseAInsertFrontExpression(AInsertFrontExpression node) {
		BType found = new SequenceType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		BType subtype;
		if (found instanceof SetType) {
			subtype = ((PairType) ((SetType) found).getSubtype()).getSecond();
		} else {
			subtype = ((SequenceType) found).getSubtype();
		}
		setType(node.getLeft(), subtype);
		setType(node.getRight(), found);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseAInsertTailExpression(AInsertTailExpression node) {
		BType found = new SequenceType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		BType subtype;
		if (found instanceof SetType) {
			subtype = ((PairType) ((SetType) found).getSubtype()).getSecond();
		} else {
			subtype = ((SequenceType) found).getSubtype();
		}
		setType(node.getLeft(), found);
		setType(node.getRight(), subtype);
		node.getLeft().apply(this);
		node.getRight().apply(this);
	}

	@Override
	public void caseARevExpression(ARevExpression node) {
		BType found = new SequenceType(new UntypedType());
		BType expected = getType(node);
		try {
			found = found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
		setType(node.getExpression(), found);
		node.getExpression().apply(this);
	}

	@Override
	public void caseAFirstExpression(AFirstExpression node) {
		setType(node.getExpression(), new SequenceType(new UntypedType()));
		node.getExpression().apply(this);

		BType s = getType(node.getExpression());
		BType subtype;
		if (s instanceof SetType) {
			subtype = ((PairType) ((SetType) s).getSubtype()).getSecond();
		} else {
			subtype = ((SequenceType) s).getSubtype();
		}
		BType expected = getType(node);
		try {
			subtype = subtype.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ subtype + "'");
		}
	}

	@Override
	public void caseALastExpression(ALastExpression node) {
		setType(node.getExpression(), new SequenceType(new UntypedType()));
		node.getExpression().apply(this);

		BType s = getType(node.getExpression());
		BType subtype;
		if (s instanceof SetType) {
			subtype = ((PairType) ((SetType) s).getSubtype()).getSecond();
		} else {
			subtype = ((SequenceType) s).getSubtype();
		}
		BType expected = getType(node);
		try {
			subtype = subtype.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ subtype + "'");
		}
	}

	/**
	 * Records
	 */

	@Override
	public void caseARecExpression(ARecExpression node) {
		StructType found = new StructType();
		found.setComplete();

		List<PRecEntry> copy = new ArrayList<PRecEntry>(node.getEntries());
		for (PRecEntry e2 : copy) {
			ARecEntry e = (ARecEntry) e2;
			setType(e.getValue(), new UntypedType());
			e.getValue().apply(this);

			AIdentifierExpression i = (AIdentifierExpression) e.getIdentifier();
			String name = Utils.getIdentifierAsString(i.getIdentifier());
			found.add(name, getType(e.getValue()));
		}
		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseARecordFieldExpression(ARecordFieldExpression node) {
		StructType s = new StructType();
		AIdentifierExpression i = (AIdentifierExpression) node.getIdentifier();
		String fieldName = Utils.getIdentifierAsString(i.getIdentifier());
		s.add(fieldName, new UntypedType());
		setType(node.getRecord(), s);
		node.getRecord().apply(this);

		BType found = ((StructType) getType(node.getRecord()))
				.getType(fieldName);
		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	@Override
	public void caseAStructExpression(AStructExpression node) {
		StructType s = new StructType();
		s.setComplete();

		List<PRecEntry> copy = new ArrayList<PRecEntry>(node.getEntries());
		for (PRecEntry e2 : copy) {
			ARecEntry e = (ARecEntry) e2;
			setType(e.getValue(), new SetType(new UntypedType()));
			e.getValue().apply(this);

			AIdentifierExpression i = (AIdentifierExpression) e.getIdentifier();
			String name = Utils.getIdentifierAsString(i.getIdentifier());
			BType t = ((SetType) getType(e.getValue())).getSubtype();
			s.add(name, t);
		}
		BType found = new SetType(s);

		BType expected = getType(node);
		try {
			found.unify(expected, this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + expected + "' , found "
					+ found + "'");
		}
	}

	/**
	 * Strings
	 */

	@Override
	public void caseAStringExpression(AStringExpression node) {
		try {
			StringType.getInstance().unify(getType(node), this);
		} catch (UnificationException e) {
			throw new TypeErrorException("Excepted '" + getType(node)
					+ "' , found " + StringType.getInstance() + "'");
		}
	}

}
