package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.exceptions.UnificationException;
import de.tlc4b.util.UtilMethods;

public class EnumeratedSetElement implements BType {
	private final String name;

	public EnumeratedSetElement(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other)) {
			throw new UnificationException();
		}
		if (other instanceof EnumeratedSetElement) {
			if (((EnumeratedSetElement) other).getName().equals(this.name)) {
				return this;
			} else {
				throw new UnificationException();
			}

		} else if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		throw new RuntimeException();
	}

	public boolean isUntyped() {
		return false;
	}

	@Override
	public String toString() {
		return name;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType)
			return true;
		if (other instanceof EnumeratedSetElement) {
			return ((EnumeratedSetElement) other).getName().equals(this.name);
		}
		return false;
	}

	public boolean containsInfiniteType() {
		return false;
	}

	public PExpression createASTNode(Typechecker typechecker) {
		AIdentifierExpression id = UtilMethods.createAIdentifierExpression(name);
		typechecker.setType(id, new SetType(this));
		return id;
	}
}
