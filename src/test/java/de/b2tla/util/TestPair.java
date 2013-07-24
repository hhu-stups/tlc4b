package de.b2tla.util;

import de.b2tla.tlc.TLCOutput;

public class TestPair {
	private final TLCOutput.TLCResult error;
	private final String path;

	public TestPair(TLCOutput.TLCResult error, String path) {
		this.error = error;
		this.path = path;
	}

	public TLCOutput.TLCResult getResult() {
		return error;
	}

	public String getPath() {
		return path;
	}
}