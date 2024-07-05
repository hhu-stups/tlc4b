package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.exceptions.UnificationException;

public class IntegerType implements BType {

	private static final IntegerType instance = new IntegerType();

	public static IntegerType getInstance() {
		return instance;
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other)) {
			throw new UnificationException();
		}
		if (other instanceof IntegerType) {
			return getInstance();
		}
		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return getInstance();
		}
		if (other instanceof IntegerOrSetOfPairType) {
			return other.unify(this, typechecker);
		}
		if (other instanceof IntegerOrSetType) {
			return other.unify(this, typechecker);
		}
		// System.out.println(other.getClass());
		throw new UnificationException();
	}

	@Override
	public String toString() {
		return "INTEGER";
	}
	
	
	public boolean isUntyped() {
		return false;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType || other instanceof IntegerType)
			return true;
		return other instanceof IntegerOrSetType
			|| other instanceof IntegerOrSetOfPairType;
	}

	public boolean containsInfiniteType() {
		return true;
	}

	public PExpression createASTNode(Typechecker typechecker) {
		AIntegerSetExpression node = new AIntegerSetExpression();
		typechecker.setType(node, new SetType(this));
		return node;
	}
}
