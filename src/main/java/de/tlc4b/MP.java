package de.tlc4b;

import java.io.OutputStream;
import java.io.PrintStream;

public class MP {
	private static final PrintStream out = System.out;
	private static final PrintStream err = System.err;

	private MP() {
	}

	public static void printlnErr(String errorMessage) {
		err.print("Error: ");
		err.println(errorMessage);
	}

	public static void printlnSilent(String message) {
		if (!TLC4BGlobals.isSilent() || TLC4BGlobals.isVerbose())
			out.println(message);
	}

	public static void printlnVerbose(String message) {
		if (TLC4BGlobals.isVerbose())
			out.println(message);
	}

	public static void printVerbose(String message) {
		if (TLC4BGlobals.isVerbose())
			out.print(message);
	}

	public static void println(String message) {
		out.println(message);
	}

	public static void print(String message) {
		out.print(message);
	}

	static class TLCOutputStream extends PrintStream {
		static final PrintStream origOut = System.out;

		public static void changeOutputStream() {
			if (TLC4BGlobals.isSilent()) {
				origOut.println("Run TLC...");
				System.setOut(new PrintStream(new OutputStream() {
					@Override
					public void write(int b) {
						// ignore
					}
				}));
				return;
			}
			System.setOut(new TLCOutputStream(origOut));
		}

		public static void resetOutputStream() {
			System.setOut(origOut);
		}

		public TLCOutputStream(OutputStream out) {
			super(out, true);
		}

		@Override
		public void print(String s) {
			s = s.replaceAll("\n", "\n> ");
			super.print("> " + s);
		}
	}

}
