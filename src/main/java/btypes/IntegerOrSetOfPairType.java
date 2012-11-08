package btypes;

public class IntegerOrSetOfPairType extends AbstractHasFollowers {

	private AbstractHasFollowers first;
	private AbstractHasFollowers second;

	public AbstractHasFollowers getFirst() {
		return first;
	}

	public AbstractHasFollowers getSecond() {
		return second;
	}

	public IntegerOrSetOfPairType() {
		UntypedType u1 = new UntypedType();
		this.first = u1;
		u1.addFollower(this);
		UntypedType u2 = new UntypedType();
		this.second = u2;
		u2.addFollower(this);
	}

	public void update(BType oldType, BType newType, ITypechecker typechecker) {
		if (newType instanceof IntegerType) {

			if (first != oldType) {
				first.deleteFollower(this);
				first.setFollowersTo(newType, typechecker);
			}

			if (second != oldType) {
				second.deleteFollower(this);
				second.setFollowersTo(newType, typechecker);
			}

			this.setFollowersTo(newType, typechecker);
			return;
		} else if (newType instanceof SetType) {
			SetType newFirst;
			SetType newSecond;
			if (this.first == oldType) {
				newFirst = (SetType) newType;
			} else {
				newFirst = new SetType(new UntypedType()).unify(this.first,
						typechecker);
			}
			if (this.second == oldType) {
				newSecond = (SetType) newType;
			} else {
				SetType set = new SetType(new UntypedType());
				second.deleteFollower(this);
				second.setFollowersTo(set, typechecker);
				newSecond = set;
			}
			SetType set = new SetType(new PairType(newFirst.getSubtype(),
					newSecond.getSubtype()));
			this.setFollowersTo(set, typechecker);
			return;
		} else if (newType instanceof UntypedType) {
			((UntypedType) newType).addFollower(this);
			if (this.first == oldType) {
				// first.deleteFollower(this);
				// first.setFollowersTo(newType, typechecker);
				first = (UntypedType) newType;
			} else if (this.second == oldType) {
				// second.deleteFollower(this);
				// second.setFollowersTo(newType, typechecker);
				second = (UntypedType) newType;
			} else {
				throw new RuntimeException();
			}
			return;
		} else if (newType instanceof IntegerOrSetOfPairType) {
			((IntegerOrSetOfPairType) newType).addFollower(this);
			if(this.first == oldType){
				first = (AbstractHasFollowers) newType;
			}else if(this.second == oldType){
				first = (AbstractHasFollowers) newType;
			}
		} else {
			throw new RuntimeException("Expectet Integer or Set");
		}
	}

	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof IntegerType) {
			this.setFollowersTo(IntegerType.getInstance(), typechecker);
			this.getFirst().deleteFollower(other);
			this.getSecond().deleteFollower(other);
			this.getFirst().setFollowersTo(IntegerType.getInstance(),
					typechecker);
			this.getSecond().setFollowersTo(IntegerType.getInstance(),
					typechecker);
			return IntegerType.getInstance();
		}
		if (other instanceof IntegerOrSetType) {
			((IntegerOrSetType) other).setFollowersTo(this, typechecker);
			return this;
		}

		throw new RuntimeException();
	}

	@Override
	public boolean isUntyped() {
		// TODO proof
		return true;
	}

}
