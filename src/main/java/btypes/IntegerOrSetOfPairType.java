package btypes;

import exceptions.TypeErrorException;

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
		IntegerOrSetType i1 = new IntegerOrSetType();
		this.first = i1;
		i1.addFollower(this);
		
		IntegerOrSetType i2 = new IntegerOrSetType();
		this.second = i2;
		i2.addFollower(this);
//		UntypedType u1 = new UntypedType();
//		this.first = u1;
//		u1.addFollower(this);
//		UntypedType u2 = new UntypedType();
//		this.second = u2;
//		u2.addFollower(this);
	}

	public void update(BType oldType, BType newType, ITypechecker typechecker) {
		

		if (newType instanceof IntegerType) {
			// if newType is an Integer then both arguments and the result are Integers
			
			first.deleteFollower(this); // 'this' is to be evaluated only once
			first.unify(IntegerType.getInstance(), typechecker);

			second.deleteFollower(this); // 'this' is to be evaluated only once
			second.unify(IntegerType.getInstance(), typechecker);

			this.setFollowersTo(IntegerType.getInstance(), typechecker); // evaluate 'this'
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
			if (this.first == oldType) {
				first = (AbstractHasFollowers) newType;
			} else if (this.second == oldType) {
				first = (AbstractHasFollowers) newType;
			}
		} else {
			throw new TypeErrorException("Expected 'INTEGER' or 'POW(_A)', found " + newType);
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
			this.getFirst().deleteFollower(this);
			this.getSecond().deleteFollower(this);
			first.unify(IntegerType.getInstance(), typechecker);
			second.unify(IntegerType.getInstance(), typechecker);
			// this.getFirst().setFollowersTo(IntegerType.getInstance(),
			// typechecker);
			// this.getSecond().setFollowersTo(IntegerType.getInstance(),
			// typechecker);
			return IntegerType.getInstance();
		}
		if (other instanceof IntegerOrSetType) {
			((IntegerOrSetType) other).setFollowersTo(this, typechecker);
			return this;
		}
		
		if(other instanceof SetType){
			first.deleteFollower(this);
			second.deleteFollower(this);
			
			first = (SetType) first.unify(new SetType(new UntypedType()), typechecker);
			second = (SetType) second.unify(new SetType(new UntypedType()), typechecker);
			
			SetType found = new SetType(new PairType(this.first,
					this.second));
			
			this.setFollowersTo(found, typechecker);

			return found.unify(other, typechecker);
		}
		
		
		System.out.println(other.getClass());
		throw new RuntimeException();
	}

	@Override
	public boolean isUntyped() {
		// TODO proof
		return true;
	}

}
