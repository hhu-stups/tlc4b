package de.b2tla.btypes;

import de.be4.classicalb.core.parser.node.PExpression;

public interface BType extends ITypeConstants{
	public BType unify(BType other, ITypechecker typechecker);
	public boolean isUntyped();
	public boolean compare(BType other);
	public String getTlaType();
	public boolean containsIntegerType();
	public PExpression createSyntaxTreeNode();
}
