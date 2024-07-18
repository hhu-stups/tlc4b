package de.tlc4b;

import org.apache.commons.cli.Options;

import java.util.HashMap;
import java.util.Map;

public class TLC4BCliOptions {

	public enum TLCOption {
		NODEAD("nodead", "do not look for deadlocks", null),
		NOTLC("notlc", "", null),
		NOTRANSLATION("notranslation", "", null),
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
		NOTRACE("notrace", "", null),
		DEL("del", "", null),
		PARINVEVAL("parinveval", "", null),
		LOG("log", "write statistics to CSV file", String.class),
		MAXINT("maxint", "", Integer.class),
		DEFAULT_SETSIZE("default_setsize", "", Integer.class),
		MININT("minint", "", Integer.class),
		WORKERS("workers", "", Integer.class),
		DFID("dfid", "depth-first model checking with iterative deepening, specify initial depth", Integer.class),
		CONSTANTSSETUP("constantssetup", "use constants found by ProB for TLC model checking", String.class),
		LTLFORMULA("ltlformula", "", String.class),
		VERBOSE("verbose", "put TLC4B in verbose mode", null),
		SILENT("silent", "put TLC4B in silent mode", null);

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
