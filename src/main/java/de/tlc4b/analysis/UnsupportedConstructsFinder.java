package de.tlc4b.analysis;

import java.io.StringWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.ACaseSubstitution;
import de.be4.classicalb.core.parser.node.AExtendsMachineClause;
import de.be4.classicalb.core.parser.node.AImplementationMachineParseUnit;
import de.be4.classicalb.core.parser.node.AImportsMachineClause;
import de.be4.classicalb.core.parser.node.AIncludesMachineClause;
import de.be4.classicalb.core.parser.node.APromotesMachineClause;
import de.be4.classicalb.core.parser.node.ARefinesModelClause;
import de.be4.classicalb.core.parser.node.ASequenceSubstitution;
import de.be4.classicalb.core.parser.node.AVarSubstitution;
import de.be4.classicalb.core.parser.node.AWhileSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.tlc4b.exceptions.NotSupportedException;

public class UnsupportedConstructsFinder extends DepthFirstAdapter {
	private final Start start;
	private static final Set<Class<? extends Node>> unsupportedClasses = new HashSet<>();

	static {
		add(ARefinesModelClause.class);
		add(AExtendsMachineClause.class);
		add(APromotesMachineClause.class);
		add(AIncludesMachineClause.class);
		add(AImportsMachineClause.class);

		add(AWhileSubstitution.class);
		add(AVarSubstitution.class);
		add(ACaseSubstitution.class);

		add(AImplementationMachineParseUnit.class);
	}

	private static void add(Class<? extends Node> clazz) {
		unsupportedClasses.add(clazz);
	}

	public UnsupportedConstructsFinder(Start start) {
		this.start = start;
	}

	public void find() {
		start.apply(this);
	}

	private static final List<String> SUM_TYPE = new LinkedList<String>(
			Arrays.asList("model_clause", "machine_clause", "substitution", "machine_parse_unit"));

	private String formatCamel(final String input) {
		StringWriter out = new StringWriter();
		char[] chars = input.toCharArray();
		for (int i = 0; i < chars.length; i++) {
			char current = chars[i];
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

}
