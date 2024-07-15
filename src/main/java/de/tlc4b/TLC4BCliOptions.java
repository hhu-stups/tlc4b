package de.tlc4b;

import org.apache.commons.cli.Options;

public class TLC4BCliOptions {

	public enum TLCOption {
		NODEAD("nodead", "do not look for deadlocks", false),
		NOTLC("notlc", "", false),
		NOTRANSLATION("notranslation", "", false),
		NOGOAL("nogoal", "do not look for GOAL predicate", false),
		NOINV("noinv", "do not look for invariant violations", false),
		NOASS("noass", "do not look for ASSERTION violations", false),
		WDCHECK("wdcheck", "", false),
		SYMMETRY("symmetry", "", false),
		TOOL("tool", "", false),
		TMP("tmp", "", false),
		NOLTL("noltl", "no checking of LTL assertions", false),
		LAZYCONSTANTS("lazyconstants", "", false),
		TESTSCRIPT("testscript", "", false),
		NOTRACE("notrace", "", false),
		DEL("del", "", false),
		PARINVEVAL("parinveval", "", false),
		LOG("log", "write statistics to CSV file", true),
		MAXINT("maxint", "", true),
		DEFAULT_SETSIZE("default_setsize", "", true),
		MININT("minint", "", true),
		WORKERS("workers", "", true),
		CONSTANTSSETUP("constantssetup", "use constants found by ProB for TLC model checking", true),
		LTLFORMULA("ltlformula", "", true),
		VERBOSE("verbose", "put TLC4B in verbose mode", false),
		SILENT("silent", "put TLC4B in silent mode", false);

		private final String arg, desc;
		private final boolean expectsArg;

		TLCOption(String arg, String desc, boolean expectsArg) {
			this.arg = arg;
			this.desc = desc;
			this.expectsArg = expectsArg;
		}

		public String arg() {
			return arg;
		}

		public String desc() {
			return desc;
		}

		public boolean expectsArg() {
			return expectsArg;
		}
	}

	static Options getCommandlineOptions() {
		Options options = new Options();
		for (TLCOption option : TLCOption.values()) {
			options.addOption(option.arg(), option.expectsArg(), option.desc());
		}
		return options;
	}

}
