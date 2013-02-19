package b2tla.btypes;

import b2tla.exceptions.UnificationException;

public class SequenceType extends AbstractHasFollowers {

	private BType subtype;

	public BType getSubtype() {
		return subtype;
	}

	public void setSubtype(BType type) {
		this.subtype = type;
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(this);
		}
	}

	public SequenceType(BType subtype) {
		setSubtype(subtype);
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other) || this.contains(other)){
			throw new UnificationException();
		}
			

		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		} else if (other instanceof SequenceType) {
			((SequenceType) other).setFollowersTo(this, typechecker);
			this.subtype = this.subtype.unify(((SequenceType) other).subtype,
					typechecker);
			return this;
		} else if (other instanceof SetType) {
			this.setFollowersTo(other, typechecker);
			SetType res = (SetType) other.unify(new SetType(new PairType(
					IntegerType.getInstance(), this.subtype)), typechecker);
			return res;
		}else if (other instanceof FunctionType){
			return other.unify(new FunctionType(IntegerType.getInstance(), this.subtype), typechecker);
		}
		throw new UnificationException();
	}

	public String toString() {
		return "SEQ(" + subtype + ")";
	}

	public boolean isUntyped() {
		return subtype.isUntyped();
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType)
			return true;
		if (other instanceof SequenceType) {
			return this.subtype.compare(((SequenceType) other).subtype);
		}
		if (other instanceof SetType) {
			SetType s = new SetType(new PairType(IntegerType.getInstance(),
					this.subtype));
			return s.compare(other);
		}
		if(other instanceof FunctionType){
			FunctionType f = new FunctionType(IntegerType.getInstance(), this.subtype);
			return f.compare(other);
		}
		return false;
	}

	@Override
	public boolean contains(BType other) {
		if (this.subtype.equals(other)) {
			return true;
		}
		if (this.subtype instanceof AbstractHasFollowers) {
			return ((AbstractHasFollowers) this.subtype).contains(other);
		}
		return false;
	}

	public String getTlaType() {
		return "Seq(" + subtype + ")";
	}

	public boolean containsIntegerType() {
		return this.subtype.containsIntegerType();
	}

}
