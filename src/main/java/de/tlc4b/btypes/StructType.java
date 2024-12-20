package de.tlc4b.btypes;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.AStructExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PRecEntry;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.tlc4b.analysis.Typechecker;
import de.tlc4b.exceptions.UnificationException;

public class StructType extends AbstractHasFollowers {

	private final LinkedHashMap<String, BType> types;
	private boolean complete;

	public StructType() {
		types = new LinkedHashMap<>();
	}

	public BType getType(String fieldName) {
		return types.get(fieldName);
	}

	public void setComplete() {
		complete = true;
	}

	public void add(String name, BType type) {
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(this);
		}
		types.put(name, type);
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		res.append("struct(");

		Iterator<Entry<String, BType>> iterator = types.entrySet().iterator();
		if (!iterator.hasNext())
			res.append("...");
		while (iterator.hasNext()) {
			Entry<String, BType> next = iterator.next();
			String fieldName = next.getKey();
			res.append(fieldName).append(":").append(next.getValue());
			if (iterator.hasNext())
				res.append(",");
		}
		res.append(")");
		return res.toString();
	}

	public void update(BType oldType, BType newType) {
		for (Entry<String, BType> next : this.types.entrySet()) {
			String name = next.getKey();
			BType type = next.getValue();
			if (type == oldType) {
				this.types.put(name, newType);
				if (newType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) newType).addFollower(this);
				}
			}

		}
	}

	public BType unify(BType other, ITypechecker typechecker) {
		if (!this.compare(other) || this.contains(other)) {
			throw new UnificationException();
		}
		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this, typechecker);
			return this;
		}
		if (other instanceof StructType) {
			StructType s = (StructType) other;

			for (Entry<String, BType> next : s.types.entrySet()) {
				String fieldName = next.getKey();
				BType sType = next.getValue();
				if (this.types.containsKey(fieldName)) {
					BType res = this.types.get(fieldName).unify(sType, typechecker);
					this.types.put(fieldName, res);
					if (res instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) res).addFollower(this);
					}
				} else {
					this.types.put(fieldName, sType);
					if (sType instanceof AbstractHasFollowers) {
						AbstractHasFollowers f = (AbstractHasFollowers) sType;
						f.deleteFollower(other);
						f.addFollower(this);
					}
				}
			}
			((StructType) other).setFollowersTo(this, typechecker);
			complete = this.complete || s.complete;
			return this;

		}
		throw new UnificationException();
	}

	public boolean isUntyped() {
		for (BType bType : types.values()) {
			if (bType.isUntyped()) {
				return true;
			}
		}
		return false;
	}

	public boolean compare(BType other) {
		if (other instanceof UntypedType) {
			return true;
		}
		if (other instanceof StructType) {
			StructType s = (StructType) other;
			Iterator<String> itr = types.keySet().iterator();
			Set<String> intersection = new HashSet<>();
			while (itr.hasNext()) {
				String temp = itr.next();
				if (s.types.containsKey(temp)) {
					intersection.add(temp);
				}
			}
			if (this.complete) {
				Set<String> temp = new HashSet<>(s.types.keySet());
				temp.removeAll(intersection);
				if (!temp.equals(new HashSet<String>())) {
					return false;
				}
			}

			if (s.complete) {
				Set<String> temp = new HashSet<>(this.types.keySet());
				temp.removeAll(intersection);
				if (!temp.equals(new HashSet<String>())) {
					return false;
				}
			}
			for (Entry<String, BType> next : types.entrySet()) {
				String name = next.getKey();
				BType value = next.getValue();
				if (!this.types.get(name).compare(value)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	@Override
	public boolean contains(BType other) {
		for (BType t : types.values()) {
			if (t.equals(other)) {
				return true;
			}
			if (t instanceof AbstractHasFollowers) {
				if (((AbstractHasFollowers) t).contains(other)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean containsInfiniteType() {
		for (BType bType : this.types.values()) {
			if (bType.containsInfiniteType())
				return true;
		}
		return false;
	}

	public PExpression createASTNode(Typechecker typechecker) {
		ArrayList<PRecEntry> list = new ArrayList<>();

		Set<Entry<String, BType>> entrySet = this.types.entrySet();
		for (Entry<String, BType> entry : entrySet) {
			String name = entry.getKey();
			BType type = entry.getValue();
			ARecEntry recEntry = new ARecEntry(new TIdentifierLiteral(name), type.createASTNode(typechecker));
			list.add(recEntry);
		}
		AStructExpression node = new AStructExpression(list);
		typechecker.setType(node, new SetType(this));
		return node;
	}

}
