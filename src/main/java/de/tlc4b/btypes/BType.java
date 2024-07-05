package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;

public interface BType {
	BType unify(BType other, ITypechecker typechecker);
	boolean isUntyped();
	boolean compare(BType other);
	boolean containsInfiniteType();
	PExpression createASTNode(Typechecker typechecker);
}
