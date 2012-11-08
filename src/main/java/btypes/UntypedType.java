package btypes;


public class UntypedType extends AbstractHasFollowers {

	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		this.setFollowersTo(other, typechecker);
		return other;
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

}
