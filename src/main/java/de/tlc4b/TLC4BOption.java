package de.tlc4b;

public enum TLC4BOption {
	NODEAD("nodead", "do not look for deadlocks", null),
	NOTLC("notlc", "do not run TLC", null),
	NOTRANSLATION("notranslation", "proceed without machine translation", null),
	NOGOAL("nogoal", "do not look for GOAL predicate", null),
	NOINV("noinv", "do not look for invariant violations", null),
	NOASS("noass", "do not look for ASSERTION violations", null),
	WDCHECK("wdcheck", "welldefinedness check", null),
	SYMMETRY("symmetry", "use symmetry", null),
	TMP("tmp", "use temp folder as output dir", null),
	NOLTL("noltl", "no checking of LTL assertions", null),
	LAZYCONSTANTS("lazyconstants", "do not wrap constants in TLCEval call", null),
	NOTRACE("notrace", "do not generate counter example trace", null),
	DEL("del", "delete on exit", null),
	PARINVEVAL("parinveval", "partial invariant evaluation", null),
	LOG("log", "write statistics to CSV file", String.class),
	MAXINT("maxint", "set value of MAXINT", Integer.class),
	DEFAULT_SETSIZE("default_setsize", "default deferred set size", Integer.class),
	MININT("minint", "set value of MININT", Integer.class),
	WORKERS("workers", "specify number of workers", Integer.class),
	DFID("dfid", "depth-first model checking with iterative deepening, specify max depth", Integer.class),
	CONSTANTSSETUP("constantssetup", "use constants found by ProB for TLC model checking", String.class),
	LTLFORMULA("ltlformula", "provide an additional LTL formula", String.class),
	VERBOSE("verbose", "put TLC4B in verbose mode", null),
	SILENT("silent", "put TLC4B in silent mode", null),
	OUTPUT("output", "provide path for output directory", String.class),
	COVERAGE("coverage", "print operation coverage", null);

	private final String arg;
	private final String desc;
	private final Class<?> expectsArg;

	TLC4BOption(String arg, String desc, Class<?> expectsArg) {
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
