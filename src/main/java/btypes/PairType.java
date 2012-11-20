package btypes;

public class PairType extends AbstractHasFollowers {

	private BType first;
	private BType second;

	public BType getFirst() {
		return this.first;
	}

	public BType getSecond() {
		return this.second;
	}

	public void setFirst(BType newType) {
		this.first = newType;
		if (newType instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) newType).addFollower(this);
		}
	}

	public void setSecond(BType newType) {
		this.second = newType;
		if (newType instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) newType).addFollower(this);
		}
	}

	public void update(BType oldType, BType newType) {
		if (this.first == oldType)
			setFirst(newType);
		if (this.second == oldType)
			setSecond(newType);
	}

	public PairType(BType first, BType second) {
		setFirst(first);
		setSecond(second);
	}

	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		if (other instanceof PairType) {
			((PairType) other).setFollowersTo(this, typechecker);
			this.first = first.unify(((PairType) other).first, typechecker);
			this.second = second.unify(((PairType) other).second, typechecker);
			return this;
		} else if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		System.out.println(other.getClass());
		throw new RuntimeException("pair");
	}

	@Override
	public String toString() {
		String res = first + "*";
		if (second instanceof PairType) {
			res += "(" + second + ")";
		} else
			res += second;
		return res;
	}

	@Override
	public boolean isUntyped() {
		if (first.isUntyped() || second.isUntyped())
			return true;
		else
			return false;
	}

}
