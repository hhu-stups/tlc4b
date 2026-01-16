package de.tlc4b.btypes;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.node.Node;

public abstract class AbstractHasFollowers implements BType {

	public abstract boolean contains(BType other);

	private final Set<Object> followers = new LinkedHashSet<>();

	public Set<Object> getFollowers() {
		return this.followers;
	}

	public void addFollower(Object obj) {
		followers.add(obj);
	}

	public void deleteFollower(Object obj) {
		followers.remove(obj);
	}

	public void setFollowersTo(BType newType, ITypechecker typechecker) {
		if (this == newType) {
			return;
		}
		Set<Object> list = new LinkedHashSet<>(followers);
		for (Object obj : list) {
			if (obj instanceof Node) {
				typechecker.setType((Node) obj, newType);
			} else if (obj instanceof SetType) {
				((SetType) obj).setSubtype(newType);
			} else if (obj instanceof IntegerOrSetOfPairType) {
				// System.out.println("this " +this + " old " + obj + " new " + newType);
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

	public String printFollower() {
		return followers.stream()
				.filter(o -> !(o instanceof Node))
				.map(o -> o.hashCode() + o.getClass().toString())
				.collect(Collectors.joining(" ", "[", "]"));
	}
}
