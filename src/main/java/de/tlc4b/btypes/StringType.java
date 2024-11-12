package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.AStringSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.exceptions.UnificationException;

public class StringType implements BType {

	private static final StringType instance = new StringType();

	public static StringType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "STRING";
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other)) {
			throw new UnificationException();
		}

		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof StringType) {
			return this;
		}

		throw new UnificationException();
	}

	public boolean isUntyped() {
		return false;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType) {
			return true;
		}
		return other instanceof StringType;
	}

	public boolean containsInfiniteType() {
		return true;
	}

	public PExpression createASTNode(Typechecker typechecker) {
		AStringSetExpression node = new AStringSetExpression();
		typechecker.setType(node, new SetType(this));
		return node;
	}

}
