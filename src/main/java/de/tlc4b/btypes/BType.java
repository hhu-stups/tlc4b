package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;

public interface BType {
	public BType unify(BType other, ITypechecker typechecker);
	public boolean isUntyped();
	public boolean compare(BType other);
	public boolean containsInfiniteType();
	public PExpression createASTNode(Typechecker typechecker);
}
