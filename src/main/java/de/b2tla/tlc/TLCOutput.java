package de.b2tla.tlc;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.b2tla.B2TLAGlobals;

public class TLCOutput {
	private final String moduleName;
	private String[] messages;
	private TLCOutputInfo tlcOutputInfo;

	Date startingTime;
	Date finishingTime;
	TLCResult result;
	ArrayList<String> states = new ArrayList<String>();
	StringBuilder trace;
	String parseError;
	int transitions = -1;
	int distinctStates = -1;

	public static enum TLCResult {
		Deadlock, Goal, InvariantViolation, ParseError, NoError, AssertionError, PropertiesError, EnumerateError, TLCError, TemporalPropertyError, WellDefinednessError
	}

	public int getTransitions() {
		return transitions;
	}

	public int getDistinctStates() {
		return distinctStates;
	}

	public long getRunningTime() {
		long time = (finishingTime.getTime() - startingTime.getTime()) / 1000;
		return time;
	}

	public TLCResult getResult() {
		return result;
	}

	public String getResultString() {
		if (result == TLCResult.InvariantViolation) {
			return "Invariant Violation";
		} else if (result == TLCResult.TemporalPropertyError) {
			return "Temporal Property Violation";
		}
		return result.toString();
	}

	public StringBuilder getErrorTrace() {
		parseTrace();
		return trace;
	}

	public String getModuleName() {
		return moduleName;
	}

	public boolean hasTrace() {
		return states.size() > 0;
	}

	public TLCOutput(String moduleName, String[] messages,
			TLCOutputInfo tlcOutputInfo) {
		this.moduleName = moduleName;
		this.messages = messages;
		this.tlcOutputInfo = tlcOutputInfo;
	}

	public void parseTLCOutput() {
		for (int i = 0; i < messages.length; i++) {
			String m = messages[i];
			if (m.startsWith("Starting...")) {
				startingTime = parseTime(m);
			} else if (m.startsWith("Finished.")) {
				finishingTime = parseTime(m);
			} else if (m.startsWith("Error:")) {
				TLCResult e = findError(m);
				if (e != null) {
					this.result = e;
				}
			} else if (m.endsWith("states left on queue.")) {
				parseStates(m);
			} else if (m.startsWith("State")) {
				states.add(m);
			} else if (m.startsWith("*** Errors:")) {
				parseError = m;
			}
		}
		if (result == null) {
			ArrayList<String> list = new ArrayList<String>(Arrays.asList(messages));
			this.result = findError(list);
		}

	}

	private void parseStates(String m) {
		final Pattern pattern = Pattern.compile("\\d+");
		final Matcher matcher = pattern.matcher(m);

		final ArrayList<Integer> ints = new ArrayList<Integer>();
		while (matcher.find()) {
			ints.add(Integer.parseInt(matcher.group()));
		}
		transitions = ints.get(0);
		distinctStates = ints.get(1);
	}

	private void parseTrace() {
		// ModuleMatcher moduleMatcher = new ModuleMatcher(moduleName,
		// ToolIO.getUserDir());

		trace = new StringBuilder();

		if (tlcOutputInfo.hasConstants()) {
			String m1 = states.get(0);
			String[] a = m1.split("/\\\\");
			Pattern pattern = Pattern.compile("\\w+");
			String constantSetup = "";
			for (int i = 1; i < a.length; i++) {
				String line = a[i];
				Matcher matcher = pattern.matcher(line);
				matcher.find();
				String identifier = matcher.group();
				if (tlcOutputInfo.isAConstant(identifier)) {
					if (!constantSetup.equals("")) {
						constantSetup += " /\\ ";
					}
					constantSetup += line;
				}
			}
			//System.out.println(constantSetup);
			if (constantSetup.equals("")) {
				/**
				 * There is only one possibility to setup the constants. As a
				 * consequence ProB has to find the values for the constants so
				 * that the predicate 1=1 is satisfied.
				 */
				trace.append("1 = 1 \n");
			} else {
				constantSetup = TLCExpressionParser.parseLine(constantSetup,
						tlcOutputInfo.getTypes());
				trace.append(constantSetup);
				trace.append("\n");
			}

		}

		for (int i = 0; i < states.size(); i++) {
			String m = states.get(i);
			// System.out.println(m);
			// String location = m.substring(0, m.indexOf("\n"));
			// String operationName = moduleMatcher.getName(location);
			int pos = m.indexOf("\n");
			if (pos == -1)
				break; // e.g. 'State 10: Stuttering'
			String predicate = m.substring(m.indexOf("\n") + 1);
			// String res = TLCExpressionParser.parseLine(predicate);
			// TODO OUTPUT
			String res = TLCExpressionParser.parseLine(predicate,
					tlcOutputInfo.getTypes());
			trace.append(res);
			trace.append("\n");
		}

	}

	public static TLCResult findError(ArrayList<String> list) {
		for (int i = 0; i < list.size(); i++) {
			String m = list.get(i);
			if (m.startsWith("In applying the function")) {
				return TLCResult.WellDefinednessError;
			} else if (m.contains("tlc2.module.TLC.Assert")) {
				return TLCResult.WellDefinednessError;
			} else if (m.startsWith("Error:") || m.startsWith("\"Error:")
					|| m.startsWith("The exception was a")) {
				System.out.println(m);
				TLCResult res = findError(m);
				if (res != null)
					return res;
			}
		}
		return TLCResult.NoError;
	}

	private static TLCResult findError(String m) {
		String[] res = m.split(" ");
		if (res[1].equals("Deadlock")) {
			return TLCResult.Deadlock;
		} else if (res[1].equals("Invariant")) {
			String invName = res[2];
			if (invName.startsWith("Invariant")) {
				return TLCResult.InvariantViolation;
			} else if (invName.equals("NotGoal")) {
				return TLCResult.Goal;
			} else if (invName.startsWith("Assertion")) {
				return TLCResult.AssertionError;
			}
		} else if (m.contains("The invariant of Assertion")) {
			return TLCResult.AssertionError;
		} else if (res[1].equals("Assumption")) {
			return TLCResult.PropertiesError;
		} else if (res[1].equals("Temporal")) {
			return TLCResult.TemporalPropertyError;
		} else if (m.equals("Error: TLC threw an unexpected exception.")) {
			return null;
		} else if (m.startsWith("Error: Attempted to apply function:")) {
			return TLCResult.WellDefinednessError;
		} else if (m.startsWith("\"Error: Invalid function call to relation")) {
			return TLCResult.WellDefinednessError;
		} else if (m.startsWith("Error: The behavior up to")) {
			return null;
		} else if (m.contains("In applying the function")) {
			return TLCResult.WellDefinednessError;
		} else if (m.startsWith("\"Error: Function assignment")) {
			return TLCResult.WellDefinednessError;
		} else if(m.startsWith("Error: Evaluating assumption")){
			return TLCResult.WellDefinednessError;
		}
		else if (m
				.startsWith("Error: The following behavior constitutes a counter-example:")) {
			return null;
		} else if (m
				.startsWith("Error: The error occurred when TLC was evaluating the nested")) {
			return null;
		} else if (m.startsWith("Error: Evaluating assumption")) {
			return null;
		} else if (m.contains("tlc2.tool.EvalException")) {
			return null;
		}

		return TLCResult.TLCError;
	}

	private static Date parseTime(String m) {
		String time = m.substring(m.indexOf("(") + 1, m.indexOf(")"));
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
		Date date;
		try {
			date = sdf.parse(time);
		} catch (ParseException e) {
			// Should never happen
			throw new RuntimeException(e);
		}
		return date;
	}
}
