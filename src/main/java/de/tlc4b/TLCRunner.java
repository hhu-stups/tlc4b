package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.MODEL_CHECKING_TIME;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.UnknownHostException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.tlc4b.tlc.TLCMessageListener;
import de.tlc4b.util.StopWatch;
import tlc2.TLCGlobals;
import util.SimpleFilenameToStream;
import util.ToolIO;
import tlc2.TLC;

public class TLCRunner {

	public static TLCMessageListener listener = null;

	public static void addTLCMessageListener(final TLCMessageListener listener) {
		TLCRunner.listener = listener;
	}

	public static void main(String[] args) {
		// this method will be executed in a separate JVM
		System.setProperty("apple.awt.UIElement", "true");
		System.out.println("Starting TLC...");
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

	private static Process startJVM(final String optionsAsString,
			final String mainClass, final String[] arguments)
			throws IOException {

		String separator = FileSystems.getDefault().getSeparator();

		String jvm = System.getProperty("java.home") + separator + "bin"
				+ separator + "java";
		String classpath = System.getProperty("java.class.path");

		List<String> command = Arrays.asList(jvm, "-cp", classpath, mainClass);
		command.addAll(Arrays.asList(arguments));

		ProcessBuilder processBuilder = new ProcessBuilder(command);
		return processBuilder.start();
	}

	public static ArrayList<String> runTLCInANewJVM(String machineName,
			String path) throws IOException {
		ArrayList<String> list = new ArrayList<>();
		list.add(path);
		list.add(machineName);
		if (!TLC4BGlobals.isDeadlockCheck()) {
			list.add("-deadlock");
		}

		if (TLC4BGlobals.isCheckLTL()) {
			list.add("-cleanup");
		}
		// list.add("-coverage");
		// list.add("1");

		String[] args = list.toArray(new String[0]);
		final Process p = startJVM("", TLCRunner.class.getCanonicalName(), args);
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
		ToolIO.setMode(ToolIO.SYSTEM);

		ArrayList<String> list = new ArrayList<>();
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
		ToolIO.setUserDir(path.getPath());
		String[] args = list.toArray(new String[0]);
		TLC tlc = new TLC();
		// handle parameters
		if (tlc.handleParameters(args)) {
			tlc.setResolver(new SimpleFilenameToStream());
			// call the actual processing method
			try {
				if (listener != null) listener.start();
				tlc.process();
				if (listener != null) listener.finish();
			} catch (Exception e) {
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
			// System.out.println(t.getId()+ " "+t.getThreadGroup());
			if (t.getName().equals("RMI Reaper")) {
				t.interrupt();
			}
		}
		// System.exit(0);
	}
}

class StreamGobbler extends Thread {
	private final InputStream is;
	private final ArrayList<String> log;

	public ArrayList<String> getLog() {
		return log;
	}

	StreamGobbler(InputStream is) {
		this.is = is;
		this.log = new ArrayList<>();
	}

	public void run() {
		try {
			InputStreamReader isr = new InputStreamReader(is, StandardCharsets.UTF_8);
			BufferedReader br = new BufferedReader(isr);
			String line;
			while ((line = br.readLine()) != null) {
				System.out.println("> " + line);
				log.add(line);
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
