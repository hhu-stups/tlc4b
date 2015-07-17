package de.tlc4b.tlc;

import java.util.ArrayList;
import java.util.Date;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import de.tlc4b.TLC4BGlobals;
import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import static tlc2.output.MP.*;
import tlc2.output.Message;
import tlc2.output.OutputCollector;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.ToolGlobals;

public class TLCResults implements ToolGlobals {

	private TLCResult tlcResult;
	private String violatedDefinition;
	private Date startTime;
	private Date endTime;
	private LinkedHashMap<String, Long> operationsCount;

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

	public LinkedHashMap<String, Long> getOperationCount() {
		return operationsCount;
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

	public String getViolatedDefinition() {
		return violatedDefinition;
	}

	public int getNumberOfTransitions() {
		return numberOfTransitions;
	}

	public int getModelCheckingTime() {
		if (endTime == null || startTime == null) {
			return -1;
		}
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

		if (TLC4BGlobals.isPrintCoverage() && OutputCollector.lineCount != null) {
			evalCoverage();
		}
	}

	private void evalCoverage() {
		Hashtable<Integer, Long> lineCount = new Hashtable<Integer, Long>();
		Set<Entry<Location, Long>> entrySet = OutputCollector.lineCount
				.entrySet();
		for (Entry<Location, Long> entry : entrySet) {
			int endline = entry.getKey().endLine();
			if (lineCount.containsKey(endline)) {
				lineCount.put(endline,
						Math.max(lineCount.get(endline), entry.getValue()));
			} else {
				lineCount.put(endline, entry.getValue());
			}
		}
		ArrayList<OpDefNode> defs = findOperations(OutputCollector.moduleNode);
		operationsCount = new LinkedHashMap<String, Long>();
		for (OpDefNode opDefNode : defs) {
			String operationName = opDefNode.getName().toString();
			Long count = lineCount.get(opDefNode.getLocation().endLine());
			if (count == null) {
				count = 0L;
			}
			operationsCount.put(operationName, count);
		}
	}

	private ArrayList<OpDefNode> findOperations(ModuleNode moduleNode) {

		OpDefNode[] opDefs = moduleNode.getOpDefs();
		ExprNode pred = null;
		for (int i = opDefs.length - 1; i > 0; i--) {
			OpDefNode def = opDefs[i];
			if (def.getName().toString().equals("Next")) {
				pred = def.getBody();
				break;
			}
		}
		OpApplNode dis = (OpApplNode) pred;
		ArrayList<OpDefNode> operations = new ArrayList<OpDefNode>();
		for (int i = 0; i < dis.getArgs().length; i++) {
			operations.add(findOperation(dis.getArgs()[i]));
		}
		return operations;
	}

	private OpDefNode findOperation(ExprOrOpArgNode arg) {
		OpApplNode op1 = (OpApplNode) arg;
		SymbolNode opNode = op1.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());
		if (opcode == OPCODE_be) { // BoundedExists
			return findOperation(op1.getArgs()[0]);
		} else if (opNode instanceof OpDefNode) {
			OpDefNode def = (OpDefNode) opNode;
			return def;
		} else {
			throw new RuntimeException("Unkown Node");
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
		switch (m.getMessageCode()) {
		case EC.TLC_INVARIANT_VIOLATED_INITIAL:
		case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
			if (m.getParameters()[0].startsWith("Assertion")) {
				tlcResult = AssertionError;
			} else if (m.getParameters()[0].equals("NotGoal")) {
				tlcResult = Goal;
			} else if (m.getParameters()[0].startsWith("ASSERT_LTL")) {
				tlcResult = TemporalPropertyViolation;
			} else {
				tlcResult = InvariantViolation;
			}
			if (m.getParameters().length > 0) {
				violatedDefinition = m.getParameters()[0];
			}
			break;

		case EC.TLC_INITIAL_STATE: {
			String arg1 = m.getParameters()[0];
			if (arg1.contains("Attempted to compute the number of elements in the overridden")) {
				// TODO
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
			if (m.getParameters().length > 0) {
				violatedDefinition = m.getParameters()[0];
			}
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
		System.out.println(params.length);
		System.out.println(params[0]);
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
				return WellDefinednessError;
			} else if (s
					.contains("CHOOSE x \\in S: P, but no element of S satisfied P")
					&& s.contains("module FunctionsAsRelations")) {
				return tlcResult = WellDefinednessError;
			} else if (s.contains("The property of ASSERT_LTL")) {
				return TemporalPropertyViolation;
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
