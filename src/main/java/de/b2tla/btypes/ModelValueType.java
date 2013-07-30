package de.b2tla.btypes;

import java.util.ArrayList;

import de.b2tla.exceptions.UnificationException;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class ModelValueType implements BType {
	private String name;

	public ModelValueType(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other)) {
			throw new UnificationException();
		}
		if (other instanceof ModelValueType) {
			if (((ModelValueType) other).getName().equals(this.name)) {
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
		if (other instanceof ModelValueType) {
			if (((ModelValueType) other).getName().equals(this.name)) {
				return true;
			}
		}
		return false;
	}

	public String getTlaType() {
		return name;
	}

	public boolean containsIntegerType() {
		return false;
	}

	public PExpression createSyntaxTreeNode() {
		TIdentifierLiteral literal = new TIdentifierLiteral(name);
		ArrayList<TIdentifierLiteral> idList = new ArrayList<TIdentifierLiteral>();
		idList.add(literal);
		AIdentifierExpression id = new AIdentifierExpression(idList);
		return id;
	}
}
