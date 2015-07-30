package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tlc4b.analysis.Typechecker;


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

	public boolean containsInfiniteType() {
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
