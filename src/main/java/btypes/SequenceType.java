package btypes;

public class SequenceType extends AbstractHasFollowers {

	private BType subtype;

	public BType getSubtype() {
		return subtype;
	}

	public void setSubtype(BType type){
		this.subtype = type;
		if(type instanceof AbstractHasFollowers){
			((AbstractHasFollowers) type).addFollower(this);
		}
	}
	
	public SequenceType(BType subtype) {
		setSubtype(subtype);
	}

	@Override
	public BType unify(BType other, ITypechecker typechecker) {
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
			SetType res =(SetType) other.unify(new SetType(new PairType(IntegerType.getInstance(),
					this.subtype)), typechecker);
			return res;
		}

		throw new RuntimeException();
	}
	
	public String toString(){
		return "Seq("+ subtype +")";
	}

	@Override
	public boolean isUntyped() {
		return subtype.isUntyped();
	}

}
