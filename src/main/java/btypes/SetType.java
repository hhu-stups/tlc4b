package btypes;

import exceptions.UnificationException;

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

	@Override
	public SetType unify(BType other, ITypechecker typechecker) {
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
		
		if(other instanceof IntegerOrSetType){
			return (SetType)other.unify(this, typechecker);
		}
		if(other instanceof SequenceType){
			return (SetType) other.unify(this, typechecker);
		}
		
		if(other instanceof IntegerOrSetOfPairType){
			return (SetType) other.unify(this, typechecker);
		}
		
		throw new UnificationException();
	}

	@Override
	public String toString() {
		return "POW("+ subtype + ")";
	}

	@Override
	public boolean isUntyped() {
		return subtype.isUntyped();
	}

}
