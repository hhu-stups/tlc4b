package de.tlc4b;

import org.apache.commons.cli.Options;

public class TLC4BCliOptions {

	public static final String NODEAD = "nodead";
	public static final String NOTLC = "notlc";
	public static final String NOTRANSLATION = "notranslation";
	public static final String NOGOAL = "nogoal";
	public static final String NOINV = "noinv";
	public static final String NOASS = "noass";
	public static final String WDCHECK = "wdcheck";
	public static final String SYMMETRY = "symmetry";
	public static final String TOOL = "tool";
	public static final String TMP = "tmp";
	public static final String NOLTL = "noltl";
	public static final String LAZYCONSTANTS = "lazyconstants";
	public static final String TESTSCRIPT = "testscript";
	public static final String NOTRACE = "notrace";
	public static final String DEL = "del";
	public static final String PARINVEVAL = "parinveval";
	public static final String LOG = "log";
	public static final String MAXINT = "maxint";
	public static final String DEFAULT_SETSIZE = "default_setsize";
	public static final String MININT = "minint";
	public static final String WORKERS = "workers";
	public static final String CONSTANTSSETUP = "constantssetup";
	public static final String LTLFORMULA = "ltlformula";
	public static final String VERBOSE = "verbose";
	public static final String SILENT = "silent";

	static Options getCommandlineOptions() {
		Options options = new Options();

		options.addOption(NODEAD, "do not look for deadlocks");
		options.addOption(NOTLC, "");
		options.addOption(NOTRANSLATION, "");
		options.addOption(NOGOAL, "do not look for GOAL predicate");
		options.addOption(NOINV, "do not look for invariant violations");
		options.addOption(NOASS, "do not look for ASSERTION violations");
		options.addOption(WDCHECK, "");
		options.addOption(SYMMETRY, "");
		options.addOption(TOOL, "");
		options.addOption(TMP, "");
		options.addOption(NOLTL, "no checking of LTL assertions");
		options.addOption(LAZYCONSTANTS, "");
		options.addOption(TESTSCRIPT, "");
		options.addOption(NOTRACE, "");
		options.addOption(DEL, "");
		options.addOption(PARINVEVAL, "");
		options.addOption(LOG, true, "write statistics to CSV file");
		options.addOption(MAXINT, true, "");
		options.addOption(DEFAULT_SETSIZE, true, "");
		options.addOption(MININT, true, "");
		options.addOption(WORKERS, true, "");
		options.addOption(CONSTANTSSETUP, true, "use constants found by ProB for TLC model checking");
		options.addOption(LTLFORMULA, true, "");
		options.addOption(VERBOSE, "put TLC4B in verbose mode");
		options.addOption(SILENT, "put TLC4B in silent mode");

		return options;
	}

}
