package de.tlc4b.util;

import de.tlc4b.TLC4B;

public class TLC4BRunnerTestString {

	public static void main(String[] args) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		TLC4B.testString(args[0],true);
	}
}
