package de.tlc4b;

import org.apache.commons.cli.Options;

public class TLC4BCliOptions {

	public enum TLCOption {
		NODEAD("nodead", "do not look for deadlocks", null),
		NOTLC("notlc", "do not run TLC", null),
		NOTRANSLATION("notranslation", "proceed without machine translation", null),
		NOGOAL("nogoal", "do not look for GOAL predicate", null),
		NOINV("noinv", "do not look for invariant violations", null),
		NOASS("noass", "do not look for ASSERTION violations", null),
		WDCHECK("wdcheck", "", null),
		SYMMETRY("symmetry", "", null),
		TOOL("tool", "", null),
		TMP("tmp", "", null),
		NOLTL("noltl", "no checking of LTL assertions", null),
		LAZYCONSTANTS("lazyconstants", "", null),
		TESTSCRIPT("testscript", "", null),
		NOTRACE("notrace", "do not generate counter example trace", null),
		DEL("del", "", null),
		PARINVEVAL("parinveval", "", null),
		LOG("log", "write statistics to CSV file", String.class),
		MAXINT("maxint", "set value of MAXINT", Integer.class),
		DEFAULT_SETSIZE("default_setsize", "", Integer.class),
		MININT("minint", "set value of MININT", Integer.class),
		WORKERS("workers", "specify number of workers", Integer.class),
		DFID("dfid", "depth-first model checking with iterative deepening, specify initial depth", Integer.class),
		CONSTANTSSETUP("constantssetup", "use constants found by ProB for TLC model checking", String.class),
		LTLFORMULA("ltlformula", "provide an additional LTL formula", String.class),
		VERBOSE("verbose", "put TLC4B in verbose mode", null),
		SILENT("silent", "put TLC4B in silent mode", null),
		OUTPUT("output", "provide path for output directory", String.class),
		COVERAGE("coverage", "print operation coverage", null);

		private final String arg, desc;
		private final Class<?> expectsArg;

		TLCOption(String arg, String desc, Class<?> expectsArg) {
			this.arg = arg;
			this.desc = desc;
			this.expectsArg = expectsArg;
		}

		public String arg() {
			return arg;
		}

		public String cliArg() {
			return "-" + arg;
		}

		public String desc() {
			return desc;
		}

		public Class<?> expectsArg() {
			return expectsArg;
		}
	}

	static Options getCommandlineOptions() {
		Options options = new Options();
		for (TLCOption option : TLCOption.values()) {
			options.addOption(option.arg(), option.expectsArg() != null, option.desc());
		}
		return options;
	}

}
