package de.tlc4b;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tla2sany.semantic.ExprNode;
import tla2sany.st.Location;

import tlc2.output.Message;
import tlc2.output.OutputCollector;

public class TLC4BGlobals {
	private static int DEFERRED_SET_SIZE;
	private static int MAX_INT;
	private static int MIN_INT;

	private static boolean checkGOAL;
	private static boolean checkDeadlock;
	private static boolean checkInvariant;
	private static boolean checkAssertion;
	private static boolean checkLTL;
	private static boolean checkWD;
	private static boolean proBconstantsSetup;
	private static boolean partialInvariantEvaluation;
	private static boolean useSymmetry;
	private static boolean printCoverage;
	private static boolean verbose;
	private static boolean silent;

	private static boolean deleteFilesOnExit;

	private static boolean runTLC;
	private static boolean translate;
	private static boolean createTraceFile;

	private static boolean forceTLCToEvalConstants;

	private static int workers;
	private static int dfid_initial_depth;

	private static final List<Message> handledMessages = new ArrayList<>();
	private static final Map<Location, Long> handledLineCounts = new HashMap<>();
	private static final List<ExprNode> handledViolatedAssumptions = new ArrayList<>();

	static {
		resetGlobals();
	}

	public static void resetGlobals() {
		DEFERRED_SET_SIZE = 3;
		MAX_INT = 3;
		MIN_INT = -1;

		checkGOAL = true;
		checkDeadlock = true;
		checkInvariant = true;
		checkAssertion = true;
		checkLTL = true;
		checkWD = true;
		partialInvariantEvaluation = false;
		useSymmetry = false;
		printCoverage = false;
		forceTLCToEvalConstants = false;
		verbose = false;
		silent = false;

		proBconstantsSetup = false;

		workers = 1;
		dfid_initial_depth = -1; // option not selected

		// for debugging purposes
		runTLC = true;
		translate = true;
		deleteFilesOnExit = false; // if enabled: deletes all created '.tla', '.cfg' files on exit of the JVM.
			// This includes the created B2TLA standard modules (e.g. Relation, but not Naturals etc.).
		createTraceFile = true;

		resetOutputCollector();
		// TODO: do we also have to reset TLCGlobals?
	}

	private static void resetOutputCollector() {
		// otherwise we will analyse old messages from previous checks -> wrong results in the same JVM (important for ProB2(-UI))
		OutputCollector.setModuleNode(null);
		OutputCollector.setInitialState(null);
		OutputCollector.setTrace(new ArrayList<>());
		handledMessages.addAll(OutputCollector.getAllMessages());
		handledLineCounts.putAll(OutputCollector.getLineCountTable());
		handledViolatedAssumptions.addAll(OutputCollector.getViolatedAssumptions());
	}

	public static List<Message> getCurrentMessages() {
		List<Message> messages = new ArrayList<>(OutputCollector.getAllMessages()); // all messages including old
		messages.removeAll(handledMessages); // remove already handled messages from old checks
		return messages;
	}

	public static Map<Location, Long> getCurrentLineCounts() {
		Map<Location, Long> lineCounts = new HashMap<>(OutputCollector.getLineCountTable());
		handledLineCounts.forEach(lineCounts::remove);
		return lineCounts;
	}

	public static List<ExprNode> getCurrentViolatedAssumptions() {
		List<ExprNode> violatedAssumptions = new ArrayList<>(OutputCollector.getViolatedAssumptions());
		violatedAssumptions.removeAll(handledViolatedAssumptions);
		return violatedAssumptions;
	}

	public static boolean isCreateTraceFile() {
		return createTraceFile;
	}

	public static void setCreateTraceFile(boolean createTraceFile) {
		TLC4BGlobals.createTraceFile = createTraceFile;
	}

	public static int getDEFERRED_SET_SIZE() {
		return DEFERRED_SET_SIZE;
	}

	public static int getMAX_INT() {
		return MAX_INT;
	}

	public static int getMIN_INT() {
		return MIN_INT;
	}

	public static boolean isGOAL() {
		return checkGOAL;
	}

	public static boolean isDeadlockCheck() {
		return checkDeadlock;
	}

	public static boolean isRunTLC() {
		return runTLC;
	}

	public static boolean isTranslate() {
		return translate;
	}

	public static boolean isInvariant() {
		return checkInvariant;
	}

	public static boolean isAssertion() {
		return checkAssertion;
	}

	public static boolean isCheckLTL() {
		return checkLTL;
	}

	public static boolean isDeleteOnExit() {
		return deleteFilesOnExit;
	}

	public static boolean isPartialInvariantEvaluation() {
		return partialInvariantEvaluation;
	}

	public static void setPartialInvariantEvaluation(boolean b) {
		partialInvariantEvaluation = b;
	}

	public static void setDEFERRED_SET_SIZE(int deferredSetSize) {
		TLC4BGlobals.DEFERRED_SET_SIZE = deferredSetSize;
	}

	public static void setMAX_INT(int maxInt) {
		TLC4BGlobals.MAX_INT = maxInt;
	}

	public static void setMIN_INT(int minInt) {
		TLC4BGlobals.MIN_INT = minInt;
	}

	public static void setGOAL(boolean goal) {
		TLC4BGlobals.checkGOAL = goal;
	}

	public static void setDeadlockCheck(boolean deadlockCheck) {
		TLC4BGlobals.checkDeadlock = deadlockCheck;
	}

	public static void setRunTLC(boolean runTLC) {
		TLC4BGlobals.runTLC = runTLC;
	}

	public static void setTranslate(boolean translate) {
		TLC4BGlobals.translate = translate;
	}

	public static void setInvariant(boolean invariant) {
		TLC4BGlobals.checkInvariant = invariant;
	}

	public static void setAssertionCheck(boolean b) {
		TLC4BGlobals.checkAssertion = b;
	}

	public static void setCheckltl(boolean checkltl) {
		TLC4BGlobals.checkLTL = checkltl;
	}

	public static void setDeleteOnExit(boolean deleteOnExit) {
		TLC4BGlobals.deleteFilesOnExit = deleteOnExit;
	}

	public static void setWorkers(int w) {
		TLC4BGlobals.workers = w;
	}

	public static int getWorkers() {
		return TLC4BGlobals.workers;
	}

	public static void setDfidInitialDepth(int depth) {
		TLC4BGlobals.dfid_initial_depth = depth;
	}

	public static int getDfidInitialDepth() {
		return TLC4BGlobals.dfid_initial_depth;
	}

	public static boolean isProBconstantsSetup() {
		return proBconstantsSetup;
	}

	public static void setProBconstantsSetup(boolean proBconstantsSetup) {
		TLC4BGlobals.proBconstantsSetup = proBconstantsSetup;
	}

	public static void setWelldefinednessCheck(boolean b) {
		TLC4BGlobals.checkWD = b;
	}

	public static boolean checkWelldefinedness() {
		return TLC4BGlobals.checkWD;
	}

	public static boolean isForceTLCToEvalConstants() {
		return forceTLCToEvalConstants;
	}

	public static void setForceTLCToEvalConstants(boolean forceTLCToEvalConstants) {
		TLC4BGlobals.forceTLCToEvalConstants = forceTLCToEvalConstants;
	}

	public static boolean useSymmetry() {
		return useSymmetry;
	}

	public static void setSymmetryUse(boolean b) {
		useSymmetry = b;
	}

	public static void setPrintCoverage(boolean b) {
		printCoverage = b;
	}

	public static boolean isPrintCoverage() {
		return printCoverage;
	}

	public static void setVerbose(boolean b) {
		verbose = b;
	}

	public static boolean isVerbose() {
		return verbose;
	}

	public static void setSilent(boolean b) {
		silent = b;
	}

	public static boolean isSilent() {
		return silent;
	}
}
