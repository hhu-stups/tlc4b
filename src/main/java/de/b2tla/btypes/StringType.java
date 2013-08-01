package de.b2tla.btypes;

import de.b2tla.analysis.Typechecker;
import de.b2tla.exceptions.UnificationException;
import de.be4.classicalb.core.parser.node.AStringSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;

public class StringType implements BType {

	private static StringType instance = new StringType();

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
		if (other instanceof StringType) {
			return true;
		}
		return false;
	}

	public String getTlaType() {
		return "STRING";
	}

	public boolean containsIntegerType() {
		return false;
	}

	public PExpression createSyntaxTreeNode(Typechecker typechecker) {
		AStringSetExpression node = new AStringSetExpression();
		typechecker.setType(node, new SetType(this));
		return node;
	}

}
