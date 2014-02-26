package de.b2tla.util;

import java.io.IOException;

import de.b2tla.B2TLA;

public class TLC4BTester {

	public static void main(String[] args) throws IOException {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		B2TLA.test(args,true);
	}

}
