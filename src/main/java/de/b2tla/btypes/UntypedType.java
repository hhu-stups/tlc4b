package de.b2tla.btypes;

import de.b2tla.analysis.Typechecker;
import de.be4.classicalb.core.parser.node.PExpression;


public class UntypedType extends AbstractHasFollowers {

	public BType unify(BType other, ITypechecker typechecker) {
		this.setFollowersTo(other, typechecker);
		return other;
	}

	public boolean isUntyped() {
		return true;
	}

	public boolean compare(BType other) {
		return true;
	}

	@Override
	public boolean contains(BType other) {
		return false;
	}

	public String getTlaType() {
		return this.toString();
	}

	public boolean containsIntegerType() {
		return false;
	}

	public PExpression createSyntaxTreeNode(Typechecker typechecker) {
		return null;
	}
	
//	@Override
//	public String toString(){
//		return "UNTYPED: Followers: "+ this.printFollower();
//	}

}
