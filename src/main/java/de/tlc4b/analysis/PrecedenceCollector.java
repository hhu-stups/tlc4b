package de.tlc4b.analysis;

import java.util.HashSet;
import java.util.Hashtable;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConvertBoolExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.ALabelPredicate;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.analysis.typerestriction.TypeRestrictor;
import de.tlc4b.btypes.BType;
import de.tlc4b.btypes.FunctionType;
import de.tlc4b.btypes.IntegerType;

public class PrecedenceCollector extends DepthFirstAdapter {

	private final static Hashtable<String, Precedence> PRECEDENCES = new Hashtable<>();

	private static void put(String s, int from, int to, boolean leftAssociative) {
		PRECEDENCES.put(s, new Precedence(s, from, to, leftAssociative));
	}

	static {

		put("AImplicationPredicate", 1, 1, false);
		put("AExistsPredicate", 1, 1, false);
		put("AForallPredicate", 1, 1, false);
		put("AEquivalencePredicate", 2, 2, false);
		put("ADisjunctPredicate", 3, 3, true); // or

		/* and **/
		put("AConjunctPredicate", 3, 3, true);
		put("APreconditionSubstitution", 3, 3, true);
		put("AAssertionSubstitution", 3, 3, true);
		put("ASelectWhenSubstitution", 3, 3, true);
		put("AParallelSubstitution", 3, 3, true);

		put("ASelectSubstitution", 3, 3, true); // and or or

		put("AEqualPredicate", 5, 5, false);
		put("ALessPredicate", 5, 5, false);
		put("AGreaterPredicate", 5, 5, false);
		put("ALessEqualPredicate", 5, 5, false);
		put("AGreaterEqualPredicate", 5, 5, false);
		put("ANotEqualPredicate", 5, 5, false);
		put("APowerOfExpression", 14, 14, false);
		put("ASubsetPredicate", 5, 5, false);
		// put("ANatural1SetExpression", 8, 8, false); // NAT \ {0}

		put("APowSubsetExpression", 8, 8, false);
		put("AUnionExpression", 8, 8, true);
		put("AIntersectionExpression", 8, 8, true);
		put("AUnionExpression", 8, 8, true);
		put("ASetSubtractionExpression", 8, 8, false);
		put("AIntervalExpression", 9, 9, true);

		put("ACartesianProductExpression", 8, 13, false);

		put("AAddExpression", 10, 10, true);

		put("AModuloExpression", 10, 11, true);
		put("AUnaryMinusExpression", 12, 12, false);
		put("AConcatExpression", 13, 13, true);
		put("ADivExpression", 13, 13, false);

		put("AFunctionExpression", 20, 20, false);

	}

	private Precedence getPrecedence(Node node) {
		String name = node.getClass().getSimpleName();
		return PRECEDENCES.get(name);
	}

	private final Hashtable<Node, Precedence> precedenceTable;
	private final HashSet<Node> brackets;
	private final Typechecker typechecker;

	public HashSet<Node> getBrackets() {
		return brackets;
	}

	public PrecedenceCollector(Start start, Typechecker typeChecker,
			MachineContext machineContext, TypeRestrictor typeRestrictor) {
		precedenceTable = new Hashtable<>();
		brackets = new HashSet<>();
		this.typechecker = typeChecker;
		start.apply(this);

		if (machineContext.getConstantsSetup() != null) {
			machineContext.getConstantsSetup().apply(this);
		}

		for (Node node : typeRestrictor.getAllRestrictedNodes()) {
			node.apply(this);
		}

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
		Node parent = node.parent();
		Precedence p = getPrecedence(node);
		if (p != null) {
			precedenceTable.put(node, p);
			if (parent instanceof ALabelPredicate) {
				parent = parent.parent();
			}

			if (parent != null) {
				Precedence parentPrecedence = precedenceTable
						.get(node.parent());
				if (Precedence.makeBrackets(p, parentPrecedence)) {
					brackets.add(node);
				}
			}
		}
		// System.out.println(node.getClass().getSimpleName() + " " + p );
	}

	public void inAConvertBoolExpression(AConvertBoolExpression node) {
		Precedence parent = PRECEDENCES.get(node.parent().getClass()
				.getSimpleName());
		if (parent != null) {
			precedenceTable.put(node, parent);
		}
	}

	@Override
	public void inAMultOrCartExpression(AMultOrCartExpression node) {
		BType type = typechecker.getType(node);

		Precedence p;
		if (type instanceof IntegerType) {
			// integer
			p = new Precedence("AMultOrCartExpression", 13, 13, true);
		} else {
			// \times
			p = new Precedence("AMultOrCartExpression", 8, 13, false);
		}
		precedenceTable.put(node, p);

		Precedence parent = precedenceTable.get(node.parent());
		if (Precedence.makeBrackets(p, parent)) {
			brackets.add(node);
		}
	}

	@Override
	public void inADomainExpression(ADomainExpression node) {
		BType type = typechecker.getType(node.getExpression());

		Precedence p;
		if (type instanceof FunctionType) {
			// Function
			p = new Precedence("ADomainExpression", 9, 9, false);

			precedenceTable.put(node, p);

			Precedence parent = precedenceTable.get(node.parent());
			if (Precedence.makeBrackets(p, parent)) {
				brackets.add(node);
			}
		}

	}

	@Override
	public void inAMinusOrSetSubtractExpression(
			AMinusOrSetSubtractExpression node) {
		BType type = typechecker.getType(node);
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
	final int from;
	final int to;
	final String name;
	final boolean leftAssociative;

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
		return parent.from > node.from;
	}

	@Override
	public String toString() {
		return from + "-" + to;
	}

}
