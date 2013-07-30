package de.b2tla.btypes;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;

import de.b2tla.exceptions.UnificationException;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.AStructExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PRecEntry;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class StructType extends AbstractHasFollowers {

	private LinkedHashMap<String, BType> types;
	private boolean complete;

	public StructType() {
		types = new LinkedHashMap<String, BType>();
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
		String res = "struct(";
		Iterator<String> keys = types.keySet().iterator();
		if (!keys.hasNext())
			res += "...";
		while (keys.hasNext()) {
			String fieldName = (String) keys.next();
			res += fieldName + ":" + types.get(fieldName);
			if (keys.hasNext())
				res += ",";
		}
		res += ")";
		return res;
	}

	public void update(BType oldType, BType newType) {
		Iterator<String> itr = this.types.keySet().iterator();
		while (itr.hasNext()) {
			String name = itr.next();
			BType t = this.types.get(name);
			if (t == oldType) {
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
			Iterator<String> itr = s.types.keySet().iterator();
			while (itr.hasNext()) {
				String fieldName = (String) itr.next();
				BType sType = s.types.get(fieldName);
				if (this.types.containsKey(fieldName)) {
					BType res = this.types.get(fieldName).unify(sType,
							typechecker);
					this.types.put(fieldName, res);
				} else {
					if (sType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) sType).addFollower(this);
					}
					this.types.put(fieldName, sType);
				}
			}
			complete = this.complete || s.complete;
			return this;

		}
		throw new UnificationException();
	}

	public boolean isUntyped() {
		Iterator<String> itr = types.keySet().iterator();
		while (itr.hasNext()) {
			if (this.types.get(itr.next()).isUntyped()) {
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
			Set<String> intersection = new HashSet<String>();
			while (itr.hasNext()) {
				String temp = itr.next();
				if (s.types.keySet().contains(temp)) {
					intersection.add(temp);
				}
			}
			if (this.complete) {
				Set<String> temp = new HashSet<String>(s.types.keySet());
				temp.removeAll(intersection);
				if (!temp.equals(new HashSet<String>())) {
					return false;
				}
			}

			if (s.complete) {
				Set<String> temp = new HashSet<String>(this.types.keySet());
				temp.removeAll(intersection);
				if (!temp.equals(new HashSet<String>())) {
					return false;
				}
			}
			Iterator<String> itr2 = types.keySet().iterator();
			while (itr2.hasNext()) {
				String name = itr2.next();
				if (!this.types.get(name).compare(s.types.get(name))) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	@Override
	public boolean contains(BType other) {
		Iterator<BType> itr = types.values().iterator();
		while (itr.hasNext()) {
			BType t = itr.next();
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

	public String getTlaType() {
		String res = "[";
		Iterator<String> keys = types.keySet().iterator();
		if (!keys.hasNext())
			res += "...";
		while (keys.hasNext()) {
			String fieldName = (String) keys.next();
			res += fieldName + ":" + types.get(fieldName);
			if (keys.hasNext())
				res += ",";
		}
		res += "]";
		return res;
	}

	public boolean containsIntegerType() {
		Iterator<BType> iterator = this.types.values().iterator();
		while (iterator.hasNext()) {
			if (iterator.next().containsIntegerType())
				return true;
		}
		return false;
	}

	public PExpression createSyntaxTreeNode() {
		ArrayList<PRecEntry> list = new ArrayList<PRecEntry>();
		for (String name : types.keySet()) {
			TIdentifierLiteral literal = new TIdentifierLiteral(name);
			ArrayList<TIdentifierLiteral> idList = new ArrayList<TIdentifierLiteral>();
			idList.add(literal);
			AIdentifierExpression id = new AIdentifierExpression(idList);
			ARecEntry entry = new ARecEntry(id, types.get(name)
					.createSyntaxTreeNode());
			list.add(entry);
		}
		return new AStructExpression(list);
	}

}
