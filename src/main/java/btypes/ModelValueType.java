package btypes;

import exceptions.UnificationException;

public class ModelValueType implements BType{
	private String name;
	
	public ModelValueType(String name){
		this.name = name;
	}
	
	public String getName(){
		return name;
	}
	
	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		if(other instanceof ModelValueType){
			if(!((ModelValueType) other).getName().equals(this.name)){
				throw new UnificationException();
			}else 
				return this;
		}else if(other instanceof UntypedType){
			((UntypedType) other).setFollowersTo(this, typechecker);
		}
		throw new UnificationException();
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	
	@Override
	public String toString(){
		return name;
	}
}
