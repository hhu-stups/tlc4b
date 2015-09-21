package de.tlc4b;

import java.io.OutputStream;
import java.io.PrintStream;

public class MP {
	private static PrintStream out = System.out;
	private static PrintStream err = System.err;

	private MP() {
	}

	public static void printlnErr(String errorMessage) {
		err.print("Error: ");
		err.println(errorMessage);
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
			MP.TLCOutputStream tlcOutputStream = new TLCOutputStream(origOut);
			System.setOut(tlcOutputStream);
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
