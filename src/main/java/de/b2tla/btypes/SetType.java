package de.b2tla.btypes;

import de.b2tla.exceptions.UnificationException;

public class SetType extends AbstractHasFollowers {

	private BType subtype;

	public SetType(BType subtype) {
		setSubtype(subtype);
	}

	public BType getSubtype() {
		return subtype;
	}

	public void setSubtype(BType type) {
		this.subtype = type;
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(this);
		}
	}

	public SetType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other) || this.contains(other))
			throw new UnificationException();

		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof SetType) {
			((SetType) other).setFollowersTo(this, typechecker);
			this.subtype = this.subtype.unify(((SetType) other).subtype,
					typechecker);
			return this;
		}

		if (other instanceof IntegerOrSetType) {
			return (SetType) other.unify(this, typechecker);
		}

		if (other instanceof IntegerOrSetOfPairType) {
			return (SetType) other.unify(this, typechecker);
		}

		if (other instanceof FunctionType) {
			return (SetType) other.unify(this, typechecker);
		}

		throw new UnificationException();
	}

	@Override
	public String toString() {
		return "POW(" + subtype + ")";
	}

	public boolean isUntyped() {
		return subtype.isUntyped();
	}

	public boolean compare(BType other) {
		if (other instanceof SetType) {
			return this.subtype.compare(((SetType) other).subtype);
		}

		if (other instanceof UntypedType)
			return true;
		if (other instanceof IntegerOrSetType
				|| other instanceof IntegerOrSetOfPairType) {
			return true;
		} else if (other instanceof FunctionType) {
			return other.compare(this);
		}
		return false;
	}

	@Override
	public boolean contains(BType other) {
		if (this.subtype.equals(other)) {
			return true;
		}
		if (this.subtype instanceof AbstractHasFollowers) {
			return ((AbstractHasFollowers) subtype).contains(other);
		}
		return false;
	}

	public String getTlaType() {
		return "SUBSET(" + subtype.getTlaType() + ")";
	}

	public boolean containsIntegerType() {
		return this.subtype.containsIntegerType();
	}

}
