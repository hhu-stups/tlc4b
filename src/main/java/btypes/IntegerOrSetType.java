package btypes;

public class IntegerOrSetType extends AbstractHasFollowers {

	public IntegerOrSetType(){
	}
	
	
	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		if(other instanceof IntegerType){
			this.setFollowersTo(IntegerType.getInstance(), typechecker);
			return IntegerType.getInstance();
		}
		if(other instanceof UntypedType){
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if(other instanceof SetType){
			this.setFollowersTo(other, typechecker);
			return other;
		}
		throw new RuntimeException();
	}


	@Override
	public boolean isUntyped() {
		// TODO proof
		return true;
	}

	
	
}
