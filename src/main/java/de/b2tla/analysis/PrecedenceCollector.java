package de.b2tla.analysis;

import java.util.HashSet;
import java.util.Hashtable;

import de.b2tla.btypes.BType;
import de.b2tla.btypes.IntegerType;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AConvertBoolExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.ANotEqualPredicate;
import de.be4.classicalb.core.parser.node.ASetSubtractionExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;

public class PrecedenceCollector extends DepthFirstAdapter {

	private final static Hashtable<String, Precedence> PRECEDENCES = new Hashtable<String, Precedence>();

	private static void put(String s, int from, int to, boolean leftAssociative) {
		PRECEDENCES.put(s, new Precedence(s, from, to, leftAssociative));
	}

	static {
		put("AEqualPredicate", 5, 5, false);
		put("AAddExpression", 10, 10, true);
		put("ADisjunctPredicate", 3, 3, true);
		put("AConjunctPredicate", 3, 3, true);
		put("AGreaterPredicate", 5, 5, false);
		put("ANatural1SetExpression", 8, 8, false); // NAT \ {0}
		put("APreconditionSubstitution", 3, 3, true);
		put("AUnionExpression", 8, 8, true);
		put("AIntervalExpression", 9, 9, true);
		put("AUnionExpression", 8, 8, true);
		put("AIntersectionExpression", 8, 8, true);
		put("AEqualPredicate", 5, 5, false);
		put("ANotEqualPredicate", 5, 5, false);
		put("AEquivalencePredicate", 2, 2, false);
		put("AAddExpression", 10, 10, true);
		put("AImplicationPredicate", 1, 1, false);
		put("ASetSubtractionExpression", 8, 8, false);
		put("AExistsPredicate", 1, 1, false);
		put("AForallPredicate", 1, 1, false);
		put("AModuloExpression",10, 11, true );
	}

	private Precedence getPrecedence(Node node) {
		String name = node.getClass().getSimpleName();
		return PRECEDENCES.get(name);
	}

	private final Hashtable<Node, Precedence> precedenceTable;
	private final HashSet<Node> brackets;
	private final Hashtable<Node, BType> typeTable;

	public HashSet<Node> getBrackets() {
		return brackets;
	}

	public PrecedenceCollector(Start start, Hashtable<Node, BType> types) {
		precedenceTable = new Hashtable<Node, Precedence>();
		brackets = new HashSet<Node>();
		typeTable = types;
		start.apply(this);
	}

	@Override
	public void caseStart(final Start node) {
		inStart(node);
		node.getPParseUnit().apply(this);
		node.getEOF().apply(this);
		outStart(node);
	}

	@Override
	public void defaultIn(final Node node) {
		Precedence p = getPrecedence(node);
		if (p != null) {
			precedenceTable.put(node, p);

			Precedence parent = precedenceTable.get(node.parent());
			if (Precedence.makeBrackets(p, parent)) {
				brackets.add(node);
			}
		}
		// System.out.println(node.getClass().getSimpleName() + " " + p );
	}

	public void inAConvertBoolExpression(AConvertBoolExpression node) {
		Precedence parent = PRECEDENCES.get(node.parent().getClass()
				.getSimpleName());
		precedenceTable.put(node, parent);
	}

	@Override
	public void inAMultOrCartExpression(AMultOrCartExpression node) {
		BType type = typeTable.get(node);

		Precedence p;
		if (type instanceof IntegerType) {
			// integer
			p = new Precedence("AMultOrCartExpression", 13, 13, true);
		} else {
			// \times
			p = new Precedence("AMultOrCartExpression", 10, 13, true);
		}
		precedenceTable.put(node, p);

		Precedence parent = precedenceTable.get(node.parent());
		if (Precedence.makeBrackets(p, parent)) {
			brackets.add(node);
		}
	}

	public void inAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		BType type = typeTable.get(node);
		Precedence p;
		if (type instanceof IntegerType) {
			// minus
			p = new Precedence("AMinusOrSetSubtractExpression", 11, 11, true);
		} else {
			// set difference
			p = new Precedence("AMinusOrSetSubtractExpression", 8, 8, false);
		}
		precedenceTable.put(node, p);

		Precedence parent = precedenceTable.get(node.parent());
		if (Precedence.makeBrackets(p, parent)) {
			brackets.add(node);
		}
	}

}

class Precedence {
	int from;
	int to;
	String name;
	boolean leftAssociative;

	public Precedence(String s, int from, int to, boolean leftAssociative) {
		this.from = from;
		this.to = to;
		this.name = s;
		this.leftAssociative = leftAssociative;
	}

	public static boolean makeBrackets(Precedence node, Precedence parent) {
		if (parent == null)
			return false;

		if (node.name.equals(parent.name)) {
			if (node.leftAssociative) {
				return false;
			}

		}
		if (node.from >= parent.from && node.from <= parent.to
				|| node.to >= parent.from && node.to <= parent.to) {
			return true;
		}
		if (parent.from > node.from)
			return true;

		return false;
	}

	@Override
	public String toString() {
		return from + "-" + to;
	}

}
