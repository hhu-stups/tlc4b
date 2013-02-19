package b2tla.btypes;


public interface BType extends ITypeConstants{
	public BType unify(BType other, ITypechecker typechecker);
	public boolean isUntyped();
	public boolean compare(BType other);
	public String getTlaType();
	public boolean containsIntegerType();
}
