package btypes;

public class IntegerType implements BType{

	private static IntegerType instance = new IntegerType();

	public static IntegerType getInstance() {
		return instance;
	}

	@Override
	public BType unify(BType other, ITypechecker typechecker) {
		if(other instanceof IntegerType){
			return getInstance();
		}
		if(other instanceof UntypedType){
			((UntypedType) other).setFollowersTo(this, typechecker);
			return getInstance();
		}
		if(other instanceof IntegerOrSetOfPairType){
			return other.unify(this, typechecker);
		}
		if(other instanceof IntegerOrSetType){
			return other.unify(this, typechecker);
		}
		System.out.println(other.getClass());
		throw new RuntimeException("Typeerror");
	}
	
	@Override
	public String toString(){
		return INTEGER;
	}

	@Override
	public boolean isUntyped() {
		return false;
	}
}
