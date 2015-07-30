package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.exceptions.UnificationException;

public class IntegerOrSetType extends AbstractHasFollowers {

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other))
			throw new UnificationException();

		if (other instanceof IntegerType) {
			this.setFollowersTo(IntegerType.getInstance(), typechecker);
			return IntegerType.getInstance();
		}
		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof SetType) {
			this.setFollowersTo(other, typechecker);
			return other;
		}
		if (other instanceof IntegerOrSetType) {
			((IntegerOrSetType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof IntegerOrSetOfPairType) {
			this.setFollowersTo(other, typechecker);
			return other;
		}
		throw new RuntimeException();
	}

	public boolean isUntyped() {
		// TODO proof
		return true;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType || other instanceof IntegerType
				|| other instanceof SetType
				|| other instanceof IntegerOrSetType
				|| other instanceof IntegerOrSetOfPairType)
			return true;
		else if (other instanceof FunctionType) {
			return other.compare(this);
		} else
			return false;
	}

	@Override
	public boolean contains(BType other) {
		return false;
	}

	public String getTlaType() {
		return null;
	}

	public boolean containsInfiniteType() {
		return false;
	}

	public PExpression createSyntaxTreeNode(Typechecker typechecker) {
		return null;
	}
}
