package de.tlc4b.analysis;

import java.io.StringWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.*;
import de.tlc4b.exceptions.NotSupportedException;

public class UnsupportedConstructsFinder extends DepthFirstAdapter {

	private static final Set<Class<? extends Node>> unsupportedClasses = new HashSet<>();

	static {
		add(ARefinesModelClause.class);
		add(AExtendsMachineClause.class);
		add(APromotesMachineClause.class);
		add(AIncludesMachineClause.class);
		add(AImportsMachineClause.class);
		add(AFreetypesMachineClause.class);

		add(AWhileSubstitution.class);
		add(AVarSubstitution.class);
		add(ACaseSubstitution.class);

		add(AImplementationMachineParseUnit.class);

		add(ARealSetExpression.class);
		add(AFloatSetExpression.class);
		add(ARealExpression.class);

		// should have been rewritten in parser
		add(AIfPredicatePredicate.class);
		add(AIfElsifPredicatePredicate.class);

		add(ALetExpressionExpression.class);
		add(ALetPredicatePredicate.class);
	}

	private static void add(Class<? extends Node> clazz) {
		unsupportedClasses.add(clazz);
	}

	private static final List<String> SUM_TYPE = new LinkedList<>(
		Arrays.asList("model_clause", "machine_clause", "machine_parse_unit", "substitution", "expression_expression", "expression", "predicate_predicate", "predicate"));

	private String formatClassName(String input) {
		StringWriter out = new StringWriter();
		char[] chars = input.toCharArray();
		for (int i = 1; i < chars.length; i++) {
			char c = chars[i];
			if (Character.isUpperCase(c)) {
				if (i > 1) {
					out.append('_');
				}
				out.append(Character.toLowerCase(c));
			} else {
				out.append(c);
			}
		}
		return out.toString();
	}

	public void defaultIn(Node node) {
		if (unsupportedClasses.contains(node.getClass())) {
			String className = node.getClass().getSimpleName();
			String formattedName = formatClassName(className);
			for (String suffix : SUM_TYPE) {
				if (formattedName.endsWith("_" + suffix)) {
					String shortName = formattedName.substring(0, formattedName.length() - suffix.length() - 1).toUpperCase(Locale.ROOT);
					String[] split = suffix.split("_");
					String type = split[split.length - 1];
					if (type.equals("clause") || type.equals("substitution") || type.equals("expression") || type.equals("predicate")) {
						throw new NotSupportedException(shortName + " " + type + " is not supported.");
					} else if (suffix.endsWith("parse_unit")) {
						throw new NotSupportedException(shortName + " parse unit is not supported.");
					} else {
						throw new NotSupportedException(shortName + " is not supported.");
					}
				}
			}
			throw new NotSupportedException(className + " is not supported.");
		}
	}

	// quick fix: ignore labels and descriptions FIXME: improve
	@Override
	public void caseALabelPredicate(ALabelPredicate node) {
		node.getPredicate().apply(this);
		node.replaceBy(node.getPredicate());
	}

	@Override
	public void caseADescriptionPredicate(ADescriptionPredicate node) {
		node.getPredicate().apply(this);
		node.replaceBy(node.getPredicate());
	}

	@Override
	public void caseADescriptionExpression(ADescriptionExpression node) {
		node.getExpression().apply(this);
		node.replaceBy(node.getExpression());
	}

	@Override
	public void caseADescriptionOperation(ADescriptionOperation node) {
		node.getOperation().apply(this);
		node.replaceBy(node.getOperation());
	}

	@Override
	public void caseADescriptionSet(ADescriptionSet node) {
		node.getSet().apply(this);
		node.replaceBy(node.getSet());
	}
}
