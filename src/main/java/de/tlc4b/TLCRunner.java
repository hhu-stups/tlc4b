package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.MODEL_CHECKING_TIME;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.tlc4b.util.StopWatch;
import util.SimpleFilenameToStream;
import util.ToolIO;
import tlc2.TLC;

public class TLCRunner {

	public static void main(String[] args) {
		// this method will be executed in a separate JVM
		System.setProperty("apple.awt.UIElement", "true");
		System.out.println("Starting TLC...");
		String path = args[0];
		ToolIO.setUserDir(path);
		String[] parameters = new String[args.length - 1];
		for (int i = 0; i < parameters.length; i++) {
			parameters[i] = args[i + 1];
		}
		try {
			TLC.main(parameters);
		} catch (UnknownHostException e) {
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}

	private static Process startJVM(final String optionsAsString,
			final String mainClass, final String[] arguments)
			throws IOException {

		String separator = System.getProperty("file.separator");

		String jvm = System.getProperty("java.home") + separator + "bin"
				+ separator + "java";
		String classpath = System.getProperty("java.class.path");

		List<String> command = new ArrayList<String>();
		command.add(jvm);
		command.add("-cp");
		command.add(classpath);
		command.add(mainClass);
		command.addAll(Arrays.asList(arguments));

		ProcessBuilder processBuilder = new ProcessBuilder(command);
		Process process = processBuilder.start();
		return process;
	}

	public static ArrayList<String> runTLCInANewJVM(String machineName,
			String path) throws IOException {
		ArrayList<String> list = new ArrayList<String>();
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

		String[] args = list.toArray(new String[list.size()]);
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
		MP.println("--------------------------------");
		MP.TLCOutputStream.changeOutputStream();
		ToolIO.setMode(ToolIO.SYSTEM);

		ArrayList<String> list = new ArrayList<String>();
		if (!TLC4BGlobals.isDeadlockCheck()) {
			list.add("-deadlock");
		}
		if (TLC4BGlobals.getWorkers() > 1) {
			list.add("-workers");
			list.add("" + TLC4BGlobals.getWorkers());
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
		String[] args = list.toArray(new String[list.size()]);
		TLC tlc = new TLC();
		// handle parameters
		if (tlc.handleParameters(args)) {
			tlc.setResolver(new SimpleFilenameToStream());
			// call the actual processing method
			try {
				tlc.process();
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
		Set<Thread> threadSet = new HashSet<Thread>(Thread.getAllStackTraces()
				.keySet());
		Thread[] threadArray = threadSet.toArray(new Thread[threadSet.size()]);
		for (int i = 0; i < threadArray.length; i++) {
			Thread t = threadArray[i];
			// System.out.println(t.getId()+ " "+t.getThreadGroup());
			if (t.getName().equals("RMI Reaper")) {
				t.interrupt();
			}
		}
		// System.exit(0);
	}
}

class StreamGobbler extends Thread {
	private InputStream is;
	private ArrayList<String> log;

	public ArrayList<String> getLog() {
		return log;
	}

	StreamGobbler(InputStream is) {
		this.is = is;
		this.log = new ArrayList<String>();
	}

	public void run() {
		try {
			InputStreamReader isr = new InputStreamReader(is, "UTF-8");
			BufferedReader br = new BufferedReader(isr);
			String line = null;
			while ((line = br.readLine()) != null) {
				System.out.println("> " + line);
				log.add(line);
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
