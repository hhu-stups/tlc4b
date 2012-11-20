package btypes;

import exceptions.UnificationException;

public class BoolType implements BType{

	private static BoolType instance = new BoolType();
	
	public static BoolType getInstance(){
		return instance;
	}
	
	@Override
	public BType unify(BType other, ITypechecker typechecker) {

		if(other instanceof BoolType){
			return this;
		}
		if(other instanceof UntypedType){
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		throw new UnificationException();
	}
	
	@Override
	public String toString(){
		return "BOOL";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

}
