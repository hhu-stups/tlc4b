package de.tlc4b.analysis;

import java.io.StringWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
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
	}

	private static void add(Class<? extends Node> clazz) {
		unsupportedClasses.add(clazz);
	}

	private static final List<String> SUM_TYPE = new LinkedList<>(
		Arrays.asList("model_clause", "machine_clause", "substitution", "machine_parse_unit"));

	private String formatCamel(final String input) {
		StringWriter out = new StringWriter();
		char[] chars = input.toCharArray();
		for (char current : chars) {
			if (Character.isUpperCase(current)) {
				out.append('_');
				out.append(Character.toLowerCase(current));
			} else {
				out.append(current);
			}
		}
		return out.toString();
	}

	public void defaultIn(Node node) {
		if (unsupportedClasses.contains(node.getClass())) {
			final String formatedName = formatCamel(node.getClass().getSimpleName());
			final String className = node.getClass().getSimpleName();
			for (final String suffix : SUM_TYPE) {
				if (formatedName.endsWith(suffix)) {
					final String shortName = formatedName.substring(3, formatedName.length() - suffix.length() - 1)
							.toUpperCase();
					final String[] split = suffix.split("_");
					final String type = split[split.length - 1];
					if (type.equals("clause") || type.equals("substitution")) {
						throw new NotSupportedException(shortName + " " + type + " is not supported.");
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
