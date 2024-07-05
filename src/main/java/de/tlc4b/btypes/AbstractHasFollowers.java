package de.tlc4b.btypes;

import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.Node;

public abstract class AbstractHasFollowers implements BType {

	public abstract boolean contains(BType other);

	private final ArrayList<Object> followers = new ArrayList<>();

	public ArrayList<Object> getFollowers() {
		return this.followers;
	}

	public void addFollower(Object obj) {
		if (!followers.contains(obj))
			followers.add(obj);
	}

	public String printFollower() {
		StringBuilder res = new StringBuilder();
		res.append("[");
		for (Object o : followers) {
			if (!(o instanceof Node)) {
				res.append(o.hashCode());
				res.append(o.getClass());
				res.append(" ");
			}
		}
		res.append("]");
		return res.toString();
	}

	public void deleteFollower(Object obj) {
		followers.remove(obj);
	}

	public void setFollowersTo(BType newType, ITypechecker typechecker) {
		if (this == newType) {
			return;
		}
		ArrayList<Object> list = new ArrayList<>(followers);
		for (Object obj : list) {
			if (obj instanceof Node) {
				typechecker.setType((Node) obj, newType);
			} else if (obj instanceof SetType) {
				((SetType) obj).setSubtype(newType);
			} else if (obj instanceof IntegerOrSetOfPairType) {
				// System.out.println("this " +this + " old " + obj + " new " +
				// newType);
				((IntegerOrSetOfPairType) obj).update(this, newType, typechecker);
			} else if (obj instanceof PairType) {
				((PairType) obj).update(this, newType);
			} else if (obj instanceof FunctionType) {
				((FunctionType) obj).update(this, newType);
			} else if (obj instanceof StructType) {
				((StructType) obj).update(this, newType);
			} else {
				throw new RuntimeException("Missing follower type: " + obj.getClass());
			}
		}
		this.followers.clear();

	}
}
