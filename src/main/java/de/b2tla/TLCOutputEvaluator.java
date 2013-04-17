package de.b2tla;

import util.ToolIO;

import de.b2tla.tlc.ModuleMatcher;
import de.b2tla.tlc.TLCExpressionParser;
import de.b2tla.util.StopWatch;

public class TLCOutputEvaluator {
	private final String moduleName;
	private ModuleMatcher moduleMatcher;

	private StringBuilder trace;

	public StringBuilder getTrace() {
		return trace;
	}

	public TLCOutputEvaluator(String moduleName, String[] messages) {
		this.moduleName = moduleName;
		//this.moduleMatcher = new ModuleMatcher(moduleName, ToolIO.getUserDir());
		StringBuilder sb = new StringBuilder();
		boolean hasTrace = false;
		for (int i = 0; i < messages.length; i++) {
			String m = messages[i];
			if (m.startsWith("State")) {
				hasTrace = true;
				String location = m.substring(0, m.indexOf("\n"));
				//String operationName = moduleMatcher.getName(location);

				String predicate = m.substring(m.indexOf("\n") + 1);
				String res = TLCExpressionParser.parseLine(predicate);
				sb.append(res);

				sb.append("\n");
			}
		}
		if (hasTrace) {
			trace = new StringBuilder();
			if (Globals.setupConstants) {
				/**
				 * There is only one possibility to setup the constants. As a
				 * consequence ProB has to find the values for the constants so
				 * that the predicate 1=1 is satisfied.
				 */
				trace.append("1 = 1 \n");
			}
			trace.append(sb);
		}
	}

}
