package de.tlc4b;

import org.apache.commons.cli.Options;

public class TLC4BCliOptions {

	static final String NODEAD = "nodead";
	static final String NOTLC = "notlc";
	static final String NOTRANSLATION = "notranslation";
	static final String NOGOAL = "nogoal";
	static final String NOINV = "noinv";
	static final String NOASS = "noass";
	static final String WDCHECK = "wdcheck";
	static final String SYMMETRY = "symmetry";
	static final String TOOL = "tool";
	static final String TMP = "tmp";
	static final String NOLTL = "noltl";
	static final String LAZYCONSTANTS = "lazyconstants";
	static final String TESTSCRIPT = "testscript";
	static final String NOTRACE = "notrace";
	static final String DEL = "del";
	static final String PARINVEVAL = "parinveval";
	static final String LOG = "log";
	static final String MAXINT = "maxint";
	static final String DEFAULT_SETSIZE = "default_setsize";
	static final String MININT = "minint";
	static final String WORKERS = "workers";
	static final String CONSTANTSSETUP = "constantssetup";
	static final String LTLFORMULA = "ltlformula";
	static final String VERBOSE = "verbose";

	static Options getCommandlineOptions() {
		Options options = new Options();

		options.addOption(NODEAD, "do not look for deadlocks (for model check, animate, execute)");
		options.addOption(NOTLC, "");
		options.addOption(NOTRANSLATION, "");
		options.addOption(NOGOAL, "");
		options.addOption(NOINV, "");
		options.addOption(NOASS, "");
		options.addOption(WDCHECK, "");
		options.addOption(SYMMETRY, "");
		options.addOption(TOOL, "");
		options.addOption(TMP, "");
		options.addOption(NOLTL, "");
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
		
		return options;
	}
	
}
