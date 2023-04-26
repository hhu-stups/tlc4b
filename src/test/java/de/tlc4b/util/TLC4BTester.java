package de.tlc4b.util;

import java.io.File;

import de.tlc4b.TLC4B;

import tlc2.TLCGlobals;

public class TLC4BTester {
	public static void main(String[] args) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows

		// The subdirectories of the states directory are named after the time when TLC was started.
		// Old versions of TLC (like the one we use) format the time with second precision only,
		// leading to name conflicts when two tests are started within the same second.
		// This line works around the issue by instead using a millisecond timestamp as the name.
		TLCGlobals.metaDir = TLCGlobals.metaRoot + File.separator + System.currentTimeMillis() + File.separator;

		TLC4B.test(args,true);
	}
}
