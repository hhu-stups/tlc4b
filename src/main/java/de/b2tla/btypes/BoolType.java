package de.b2tla.btypes;

import de.b2tla.exceptions.UnificationException;

public class BoolType implements BType {

	private static BoolType instance = new BoolType();

	public static BoolType getInstance() {
		return instance;
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if(!this.compare(other))
			throw new UnificationException();
		
		if (other instanceof BoolType) {
			return this;
		}
		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		throw new UnificationException();
	}

	@Override
	public String toString() {
		return "BOOL";
	}

	public boolean isUntyped() {
		return false;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType || other instanceof BoolType)
			return true;
		else
			return false;
	}

	public String getTlaType() {
		return "BOOLEAN";
	}

	public boolean containsIntegerType() {
		return false;
	}

}
