package analysis;

import java.util.HashSet;
import java.util.Hashtable;

import btypes.BType;




import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
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
		System.out.println(brackets);
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

			Precedence parent = PRECEDENCES.get(node.parent().getClass()
					.getSimpleName());
			if (parent != null) {
				if (p.overlap(parent)) {
					brackets.add(node);
				}
			}
		}
		// System.out.println(node.getClass().getSimpleName() + " " + p);
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

	public boolean overlap(Precedence other) {

		if (name.equals(other.name)) {
			if (leftAssociative) {
				return false;
			}

		}
		if (from >= other.from && from <= other.to || to >= other.from
				&& to <= other.to) {
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return from + "-" + to;
	}
}
