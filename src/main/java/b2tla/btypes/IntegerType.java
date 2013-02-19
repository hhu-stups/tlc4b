package b2tla.btypes;

import b2tla.exceptions.UnificationException;

public class IntegerType implements BType {

	private static IntegerType instance = new IntegerType();

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
	
	public String getTlaType() {
		return "Int";
	}

	public boolean isUntyped() {
		return false;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType || other instanceof IntegerType)
			return true;
		if (other instanceof IntegerOrSetType
				|| other instanceof IntegerOrSetOfPairType)
			return true;
		return false;
	}

	public boolean containsIntegerType() {
		return true;
	}
}
