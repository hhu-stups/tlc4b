package de.tlc4b.tlc;

import java.util.ArrayList;
import java.util.Date;

import de.tlc4b.TLC4BGlobals;
import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import tlc2.output.EC;
import static tlc2.output.MP.*;
import tlc2.output.Message;
import tlc2.output.OutputCollector;
import tlc2.tool.TLCStateInfo;

public class TLCResults {

	private TLCResult tlcResult;
	private Date startTime;
	private Date endTime;

	private int lengthOfTrace;
	private String traceString;

	private int numberOfDistinctStates;
	private int numberOfTransitions;

	private TLCOutputInfo tlcOutputInfo;

	public static enum TLCResult {
		Deadlock, Goal, InvariantViolation, ParseError, NoError, AssertionError, PropertiesError, EnumerationError, TLCError, TemporalPropertyViolation, WellDefinednessError, InitialStateError;
	}

	public boolean hasTrace() {
		return lengthOfTrace > 0;
	}

	public TLCResults(TLCOutputInfo tlcOutputInfo) {
		this.tlcOutputInfo = tlcOutputInfo;
		this.lengthOfTrace = 0;
	}

	public int getNumberOfDistinctStates() {
		return numberOfDistinctStates;
	}

	public String getTrace() {
		return traceString;
	}

	public int getNumberOfTransitions() {
		return numberOfTransitions;
	}

	public int getModelCheckingTime() {
		return (int) (endTime.getTime() - startTime.getTime()) / 1000;
	}

	public void evalResults() {

		evalAllMessages();

		if (hasTrace()
				|| (TLC4BGlobals.getTestingMode() && OutputCollector
						.getInitialState() != null)) {
			evalTrace();
		}

		if (tlcResult == NoError && tlcOutputInfo.hasInitialisation()
				&& numberOfDistinctStates == 0) {
			// Can not setup constants
			tlcResult = InitialStateError;
		}

	}

	private void evalTrace() {
		ArrayList<TLCStateInfo> trace = OutputCollector.getTrace();
		TracePrinter printer = null;
		if (trace != null) {
			printer = new TracePrinter(trace, tlcOutputInfo);
		} else if (OutputCollector.getInitialState() != null) {
			printer = new TracePrinter(OutputCollector.getInitialState(),
					tlcOutputInfo);
		}
		if (printer != null) {
			traceString = printer.getTrace().toString();
		}
	}

	private void evalAllMessages() {

		ArrayList<Message> messages = OutputCollector.getAllMessages();
		for (Message m : messages) {
			switch (m.getMessageClass()) {
			case ERROR:
				evalErrorMessage(m);
				break;
			case TLCBUG:
				break;
			case STATE:
				lengthOfTrace++;
				break;
			case WARNING:
				break;
			case NONE:
				evalStatusMessage(m);
				break;
			default:
				break;
			}
		}

		if (this.tlcResult == null) {
			// this.tlcResult = TLCError;
		}

	}

	private void evalStatusMessage(Message m) {

		switch (m.getMessageCode()) {

		case EC.TLC_STARTING:
			startTime = m.getDate();
			break;
		case EC.TLC_FINISHED:
			endTime = m.getDate();
			break;

		case EC.TLC_STATS:
			numberOfTransitions = Integer.parseInt(m.getParameters()[0]);
			numberOfDistinctStates = Integer.parseInt(m.getParameters()[1]);
			break;

		case EC.TLC_STATS_DFID:

			break;

		case EC.TLC_SUCCESS:
			tlcResult = TLCResult.NoError;
			break;

		default:
			break;
		}

	}

	private void evalErrorMessage(Message m) {
//		System.out.println(------------------);
//		System.out.print(m.getMessageCode() + " " + m.getParameters().length);
//		for (int i = 0; i < m.getParameters().length; i++) {
//			System.out.print(" " + m.getParameters()[i]);
//		}
//		System.out.println();
		switch (m.getMessageCode()) {
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
			if (m.getParameters()[0].startsWith("Assertion")) {
				tlcResult = AssertionError;
			} else if (m.getParameters()[0].equals("NotGoal")) {
				tlcResult = Goal;
			} else {
				tlcResult = TLCResult.InvariantViolation;
			}
			break;

		case EC.TLC_INITIAL_STATE: {
			String arg1 = m.getParameters()[0];
			if (arg1.contains("Attempted to compute the number of elements in the overridden")) {

			}
			tlcResult = EnumerationError;
			return;
		}

		case EC.TLC_DEADLOCK_REACHED:
			tlcResult = TLCResult.Deadlock;
			break;

		case EC.TLC_ASSUMPTION_FALSE:
			tlcResult = TLCResult.PropertiesError;
			break;

		case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
			tlcResult = TLCResult.TemporalPropertyViolation;
			break;

		case EC.TLC_ASSUMPTION_EVALUATION_ERROR:
			tlcResult = evaluatingParameter(m.getParameters());
			break;

		case EC.TLC_VALUE_ASSERT_FAILED:
			tlcResult = WellDefinednessError;
			break;

		case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE:
			if (m.getParameters()[0].contains("tlc2.module.TLC.Assert")) {
				tlcResult = WellDefinednessError;
			}
			break;

		case EC.GENERAL:
			tlcResult = evaluatingParameter(m.getParameters());
			break;

		default:
			break;
		}
	}

	private TLCResult evaluatingParameter(String[] params) {
		for (int i = 0; i < params.length; i++) {
			String s = params[i];
			if (s.contains("not enumerable")) {
				return EnumerationError;
			} else if (s.contains("The invariant of Assertion")) {
				return AssertionError;
			} else if (s.contains("The invariant of Invariant")) {
				return InvariantViolation;
			} else if (s.contains("In applying the function")) {
				return WellDefinednessError;
			} else if (s.contains("which is not in the domain of the function")) {
				return WellDefinednessError;
			} else if (s.contains("tlc2.module.TLC.Assert")) {
				return tlcResult = WellDefinednessError;
			} else if (s
					.contains("CHOOSE x \\in S: P, but no element of S satisfied P")
					&& s.contains("module FunctionsAsRelations")) {
				return tlcResult = WellDefinednessError;
			}

		}
		// unkown error
		return null;
	}

	public TLCResult getTLCResult() {
		return tlcResult;
	}

	public String getResultString() {
		if (tlcResult == TLCResult.InvariantViolation) {
			return "Invariant Violation";
		} else if (tlcResult == TLCResult.TemporalPropertyViolation) {
			return "Temporal Property Violation";
		}
		if (tlcResult == null) {
			return TLCError.toString();
		}
		return tlcResult.toString();
	}
}
