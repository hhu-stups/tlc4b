package de.tlc4b.analysis.transformation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.LinkedList;

import de.be4.classicalb.core.parser.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.ACoupleExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AEventBComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.Start;

public class SetComprehensionOptimizer extends DepthFirstAdapter {

	public static void optimizeSetComprehensions(Start start) {
		SetComprehensionOptimizer optimizer = new SetComprehensionOptimizer();
		start.apply(optimizer);
	}

	@Override
	public void caseAComprehensionSetExpression(AComprehensionSetExpression node) {
		if (node.parent() instanceof ADomainExpression) {
			LinkedList<PExpression> identifiers = node.getIdentifiers();

			final ArrayList<String> list = new ArrayList<String>();
			final AIdentifierExpression last = (AIdentifierExpression) identifiers
					.getLast();
			for (int i = 0; i < identifiers.size() - 1; i++) {
				AIdentifierExpression id = (AIdentifierExpression) identifiers
						.get(i);
				String name = Utils.getIdentifierAsString(id.getIdentifier());
				list.add(name);
			}

			Hashtable<String, PExpression> values = new Hashtable<String, PExpression>();
			ArrayList<AEqualPredicate> equalList = new ArrayList<AEqualPredicate>();
			analysePredicate(node.getPredicates(), list, values, equalList);

			if (values.keySet().containsAll(list)) {
				// delete nodes
				new NodesRemover(node.getPredicates(), equalList, values);

				AEventBComprehensionSetExpression eventBcomprehension = new AEventBComprehensionSetExpression();
				ArrayList<PExpression> ids = new ArrayList<PExpression>();
				ids.add(last);
				eventBcomprehension.setIdentifiers(ids);

				ACoupleExpression couple = new ACoupleExpression();

				ArrayList<PExpression> exprs = new ArrayList<PExpression>();
				for (int i = 0; i < list.size(); i++) {
					exprs.add(values.get(list.get(i)));
				}
				couple.setList(exprs);
				eventBcomprehension.setExpression(couple);

				AMemberPredicate member = new AMemberPredicate();
				member.setLeft((AIdentifierExpression) last.clone());
				AComprehensionSetExpression compre = new AComprehensionSetExpression();
				ArrayList<PExpression> ids2 = new ArrayList<PExpression>();
				ids2.add((AIdentifierExpression) last.clone());
				compre.setIdentifiers(ids2);
				compre.setPredicates(node.getPredicates());
				member.setRight(compre);
				eventBcomprehension.setPredicates(member);

				node.parent().replaceBy(eventBcomprehension);

				eventBcomprehension.apply(this);
			}
		}

		if (node.parent() != null)
			testGeneric(node);

	}

	private void testGeneric(AComprehensionSetExpression node) {
		final LinkedList<PExpression> identifiers = node.getIdentifiers();
		final ArrayList<String> list = new ArrayList<String>();
		final Hashtable<String, AIdentifierExpression> identifierTable = new Hashtable<String, AIdentifierExpression>();
		for (int i = 0; i < identifiers.size(); i++) {
			AIdentifierExpression id = (AIdentifierExpression) identifiers
					.get(i);
			String name = Utils.getIdentifierAsString(id.getIdentifier());
			list.add(name);
			identifierTable.put(name, id);
		}

		Hashtable<String, PExpression> values = new Hashtable<String, PExpression>();
		ArrayList<AEqualPredicate> equalList = new ArrayList<AEqualPredicate>();
		analysePredicate(node.getPredicates(), list, values, equalList);
		if (values.size() > 0 && list.size()-values.size() > 0) {
			// delete nodes
			new NodesRemover(node.getPredicates(), equalList, values);

			AEventBComprehensionSetExpression eventBcomprehension = new AEventBComprehensionSetExpression();
			ArrayList<PExpression> ids = new ArrayList<PExpression>();
			ArrayList<PExpression> ids2 = new ArrayList<PExpression>();
			ArrayList<PExpression> ids3 = new ArrayList<PExpression>();
			for (String p : list) {
				if (!values.containsKey(p)) {
					PExpression clone = (PExpression) identifierTable.get(p)
							.clone();
					ids.add(clone);
					PExpression clone2 = (PExpression) identifierTable.get(p)
							.clone();
					ids2.add(clone2);
					PExpression clone3 = (PExpression) identifierTable.get(p)
							.clone();
					ids3.add(clone3);
				}
			}
			eventBcomprehension.setIdentifiers(ids);

			ACoupleExpression couple = new ACoupleExpression();
			ArrayList<PExpression> exprs = new ArrayList<PExpression>();
			for (int i = 0; i < list.size(); i++) {
				String name = list.get(i);
				if (values.containsKey(name)) {
					exprs.add(values.get(name));
				} else {
					PExpression clone = (PExpression) identifierTable.get(name)
							.clone();
					exprs.add(clone);
				}

			}
			couple.setList(exprs);
			eventBcomprehension.setExpression(couple);

			AMemberPredicate member = new AMemberPredicate();
			if (ids2.size() > 1) {
				ACoupleExpression couple2 = new ACoupleExpression();
				couple2.setList(ids2);
				member.setLeft(couple2);
			} else {
				member.setLeft(ids2.get(0));
			}

			AComprehensionSetExpression compre = new AComprehensionSetExpression();
			compre.setIdentifiers(ids3);
			compre.setPredicates(node.getPredicates());
			member.setRight(compre);
			eventBcomprehension.setPredicates(member);

			node.replaceBy(eventBcomprehension);

			eventBcomprehension.apply(this);
		}

	}

	private void analysePredicate(PPredicate predicate, ArrayList<String> list,
			Hashtable<String, PExpression> values,
			ArrayList<AEqualPredicate> equalList) {
		if (predicate instanceof AConjunctPredicate) {
			AConjunctPredicate con = (AConjunctPredicate) predicate;
			analysePredicate(con.getLeft(), list, values, equalList);
			analysePredicate(con.getRight(), list, values, equalList);
		} else if (predicate instanceof AEqualPredicate) {
			AEqualPredicate equal = (AEqualPredicate) predicate;
			if (equal.getLeft() instanceof AIdentifierExpression) {
				AIdentifierExpression id = (AIdentifierExpression) equal
						.getLeft();
				String name = Utils.getIdentifierAsString(id.getIdentifier());
				if (list.contains(name) && !values.containsKey(name)) {
					if (equal.getRight() instanceof AIdentifierExpression) {
						AIdentifierExpression id2 = (AIdentifierExpression) equal
								.getRight();
						String name2 = Utils.getIdentifierAsString(id2
								.getIdentifier());
						if (values.containsKey(name2)){
							return;
						}
					}
					equalList.add(equal);
					values.put(name, equal.getRight());
				}
			} else if (!equalList.contains(equal)
					&& equal.getRight() instanceof AIdentifierExpression) {
				AIdentifierExpression id = (AIdentifierExpression) equal
						.getRight();
				String name = Utils.getIdentifierAsString(id.getIdentifier());
				if (list.contains(name) && !values.containsKey(name)) {
					if (equal.getLeft() instanceof AIdentifierExpression) {
						AIdentifierExpression id2 = (AIdentifierExpression) equal
								.getLeft();
						String name2 = Utils.getIdentifierAsString(id2
								.getIdentifier());
						if (values.contains(name2))
							return;
					}
					equalList.add(equal);
					values.put(name, equal.getLeft());
				}
			}

		}
	}

	class NodesRemover extends DepthFirstAdapter {
		final ArrayList<AEqualPredicate> removeList;
		final Hashtable<String, PExpression> values;

		public NodesRemover(PPredicate predicate,
				ArrayList<AEqualPredicate> equalList,
				Hashtable<String, PExpression> values) {
			this.removeList = equalList;
			this.values = values;

			for (AEqualPredicate pred : removeList) {
				pred.replaceBy(null);
			}

			predicate.apply(this);

		}

		@Override
		public void caseAConjunctPredicate(AConjunctPredicate node) {
			if (node.getLeft() != null) {
				node.getLeft().apply(this);
			}
			if (node.getRight() != null) {
				node.getRight().apply(this);
			}
			outAConjunctPredicate(node);
		}

		@Override
		public void outAConjunctPredicate(AConjunctPredicate node) {
			if (node.parent() != null) {
				if (node.getLeft() == null && node.getRight() == null) {
					node.replaceBy(null);
				} else if (node.getLeft() == null) {
					PPredicate right = node.getRight();
					node.replaceBy(right);
				} else if (node.getRight() == null) {
					node.replaceBy(node.getLeft());
				}
			}
		}

		@Override
		public void caseAIdentifierExpression(AIdentifierExpression node) {
			String name = Utils.getIdentifierAsString(node.getIdentifier());

			PExpression value = values.get(name);
			if (value != null) {
				node.replaceBy((PExpression) value.clone());
			}

		}
	}

}
