package de.b2tla.util;

import de.b2tla.tlc.TLCResults.TLCResult;


public class TestPair {
	private final TLCResult error;
	private final String path;

	public TestPair(TLCResult error, String path) {
		this.error = error;
		this.path = path;
	}

	public TLCResult getResult() {
		return error;
	}

	public String getPath() {
		return path;
	}
}