package de.b2tla;

public class B2TLAGlobals {
	private static int DEFERRED_SET_SIZE;
	private static int MAX_INT;
	private static int MIN_INT;

	private static boolean checkGOAL;
	private static boolean checkDeadlock;
	private static boolean checkInvariant;
	private static boolean checkLTL;
	
	private static boolean deleteFilesOnExit;
	
	private static boolean runTLC;
	private static boolean translate;
	private static boolean hideTLCConsoleOutput;


	static {
		resetGlobals();
	}

	public static void resetGlobals() {
		DEFERRED_SET_SIZE = 3;
		MAX_INT = 4;
		MIN_INT = -1;

		checkGOAL = true;
		checkDeadlock = true;
		checkInvariant = true;
		checkLTL = true;

		// for debugging purposes
		runTLC = true;
		translate = true;
		hideTLCConsoleOutput = false; // is mapped to TOOLIO.tool
		deleteFilesOnExit = false; // if enabled: deletes all created '.tla',
									// '.cfg' files on exit of the JVM. This includes
									// the created B2TLA standard modules (e.g.
									// Relation, but not Naturals etc.).
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

	public static boolean isCheckltl() {
		return checkLTL;
	}

	public static boolean isTool() {
		return hideTLCConsoleOutput;
	}

	public static boolean isDeleteOnExit() {
		return deleteFilesOnExit;
	}

	public static void setDEFERRED_SET_SIZE(int dEFERRED_SET_SIZE) {
		DEFERRED_SET_SIZE = dEFERRED_SET_SIZE;
	}

	public static void setMAX_INT(int mAX_INT) {
		MAX_INT = mAX_INT;
	}

	public static void setMIN_INT(int mIN_INT) {
		MIN_INT = mIN_INT;
	}

	public static void setGOAL(boolean gOAL) {
		checkGOAL = gOAL;
	}

	public static void setDeadlockCheck(boolean deadlockCheck) {
		B2TLAGlobals.checkDeadlock = deadlockCheck;
	}

	public static void setRunTLC(boolean runTLC) {
		B2TLAGlobals.runTLC = runTLC;
	}

	public static void setTranslate(boolean translate) {
		B2TLAGlobals.translate = translate;
	}

	public static void setInvariant(boolean invariant) {
		B2TLAGlobals.checkInvariant = invariant;
	}

	public static void setCheckltl(boolean checkltl) {
		B2TLAGlobals.checkLTL = checkltl;
	}

	public static void setTool(boolean tool) {
		B2TLAGlobals.hideTLCConsoleOutput = tool;
	}

	public static void setDeleteOnExit(boolean deleteOnExit) {
		B2TLAGlobals.deleteFilesOnExit = deleteOnExit;
	}

}
