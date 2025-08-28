package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.MODEL_CHECKING_TIME;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import de.tlc4b.tlc.TLCMessageListener;
import de.tlc4b.util.StopWatch;
import tlc2.TLCGlobals;
import tlc2.tool.fp.FPSetFactory;
import util.SimpleFilenameToStream;
import util.ToolIO;
import tlc2.TLC;

public final class TLCRunner {

	public static TLCMessageListener listener = null;

	private TLCRunner() {
		throw new AssertionError();
	}

	public static void addTLCMessageListener(final TLCMessageListener listener) {
		TLCRunner.listener = listener;
	}

	/**
	 * Don't call yourself, use {@link TLCRunner#runTLCInANewJVM(String, String)}
	 */
	public static void main(String[] args) {
		// this method will be executed in a separate JVM
		System.setProperty("apple.awt.UIElement", "true");
		System.out.println("Starting TLC...");
		ToolIO.reset();
		ToolIO.setMode(ToolIO.SYSTEM);
		String path = args[0];
		ToolIO.setUserDir(path);
		String[] parameters = new String[args.length - 1];
		System.arraycopy(args, 1, parameters, 0, parameters.length);
		try {
			TLC.main(parameters);
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	private static Process startJVM(final String mainClass, final List<String> arguments)
			throws IOException {

		boolean isWindows = System.getProperty("os.name").toLowerCase(Locale.ROOT).startsWith("windows");
		String jvm = System.getProperty("java.home") + File.separator + "bin" + File.separator + (isWindows ? "java.exe" : "java");
		String classpath = System.getProperty("java.class.path");

		List<String> command = new ArrayList<>();
		command.add(jvm);
		command.addAll(Arrays.asList("-XX:+UseParallelGC", "-Dfile.encoding=UTF-8", "-Dtlc2.tool.fp.FPSet.impl=" + FPSetFactory.getImplementationDefault()));
		command.add(mainClass);
		command.addAll(arguments);

		ProcessBuilder processBuilder = new ProcessBuilder(command);
		processBuilder.environment().put("CLASSPATH", classpath);
		return processBuilder.start();
	}

	private static List<String> buildTlcArgs(String machineName) {
		List<String> list = new ArrayList<>();
		if (!TLC4BGlobals.isDeadlockCheck()) {
			list.add("-deadlock");
		}
		if (TLC4BGlobals.getWorkers() > 1) {
			list.add("-workers");
			list.add("" + TLC4BGlobals.getWorkers());
		} else {
			// When running multiple model checks from ProB2, the global state is not reset.
			// Reset number of workers manually here, are there any other problematic options?!
			TLCGlobals.setNumWorkers(1);
		}
		if (TLC4BGlobals.getDfidInitialDepth() >= 0) {
			list.add("-dfid");
			list.add("" + TLC4BGlobals.getDfidInitialDepth());
		} else {
			// When running multiple model checks from ProB2, the global state is not reset.
			// Reset DFID manually here if not selected, are there any other problematic options?!
			TLCGlobals.DFIDMax = -1;
		}

		if (TLC4BGlobals.isPrintCoverage()) {
			list.add("-nowarning");
			list.add("-coverage");
			list.add("" + 60);
		}

		list.add("-maxSetSize");
		list.add("100000000");


		// list.add("-config");
		// list.add(machineName + ".cfg");
		list.add(machineName);

		return list;
	}

	public static List<String> runTLCInANewJVM(String machineName, String path) throws IOException {
		List<String> list = buildTlcArgs(machineName);
		list.add(0, path); // userdir must be first arg

		final Process p = startJVM(TLCRunner.class.getCanonicalName(), list);
		StreamGobbler stdOut = new StreamGobbler(p.getInputStream());
		stdOut.start();
		StreamGobbler errOut = new StreamGobbler(p.getErrorStream());
		errOut.start();
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		return stdOut.getLog();
	}

	public static void runTLC(String machineName, File path) {
		StopWatch.start(MODEL_CHECKING_TIME);
		MP.printlnSilent("--------------------------------");
		MP.TLCOutputStream.changeOutputStream();
		ToolIO.reset();
		ToolIO.setMode(ToolIO.SYSTEM);
		ToolIO.setUserDir(path.getPath());

		String[] args = buildTlcArgs(machineName).toArray(new String[0]);
		TLC tlc = new TLC();
		// handle parameters
		if (tlc.handleParameters(args)) {
			tlc.setResolver(new SimpleFilenameToStream());
			// call the actual processing method
			try {
				if (listener != null) listener.start();
				tlc.process();
				if (listener != null) listener.finish();
			} catch (Exception ignored) {
			}
		}
		// System.setOut(systemOut);
		// ArrayList<String> messages = btlcStream.getArrayList();
		closeThreads();
		// return messages;
		MP.TLCOutputStream.resetOutputStream();
		MP.println("--------------------------------");
		StopWatch.stop(MODEL_CHECKING_TIME);
	}

	private static void closeThreads() {
		Set<Thread> threadSet = new HashSet<>(Thread.getAllStackTraces().keySet());
		Thread[] threadArray = threadSet.toArray(new Thread[0]);
		for (Thread t : threadArray) {
			if (t.getName().equals("RMI Reaper")) {
				t.interrupt();
			}
		}
	}
}

final class StreamGobbler extends Thread {

	private final InputStream is;
	private final ArrayList<String> log;

	public ArrayList<String> getLog() {
		return log;
	}

	StreamGobbler(InputStream is) {
		super("StreamGobbler for " + is);
		this.is = is;
		this.log = new ArrayList<>();
		this.setDaemon(true);
	}

	public void run() {
		try {
			InputStreamReader isr = new InputStreamReader(is, StandardCharsets.UTF_8);
			BufferedReader br = new BufferedReader(isr);
			String line;
			while ((line = br.readLine()) != null) {
				if (TLC4BGlobals.isVerbose()) {
					System.out.println("> " + line);
				}
				log.add(line);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
