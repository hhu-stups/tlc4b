package btypes;


public interface BType extends ITypeConstants{
	public BType unify(BType other, ITypechecker typechecker);
	public boolean isUntyped();
}
