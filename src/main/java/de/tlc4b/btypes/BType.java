package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;

public interface BType extends ITypeConstants{
	public BType unify(BType other, ITypechecker typechecker);
	public boolean isUntyped();
	public boolean compare(BType other);
	public String getTlaType();
	public boolean containsInfiniteType();
	public PExpression createSyntaxTreeNode(Typechecker typechecker);
}
