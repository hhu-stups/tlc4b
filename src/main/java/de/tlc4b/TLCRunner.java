package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.MODEL_CHECKING_TIME;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import de.tlc4b.util.StopWatch;
import tlc2.TLCGlobals;
import tlc2.output.Message;
import tlc2.tool.fp.FPSetFactory;
import util.SimpleFilenameToStream;
import util.ToolIO;
import tlc2.TLC;

public final class TLCRunner {

	private static TLCMessageHandler handler = null;

	private TLCRunner() {
		throw new AssertionError();
	}

	public static void setTLCMessageHandler(TLCMessageHandler handler) {
		if (TLCRunner.handler != null) {
			try {
				TLCRunner.handler.close();
			} catch (Exception ignored){
			}
		}
		TLCRunner.handler = handler;
	}

	/**
	 * Don't call this yourself, use {@link TLCRunner#runTLCInANewJVM(String, File)} instead.
	 */
	public static void main(String[] args) throws Exception {
		// this method will be executed in a separate JVM
		System.setProperty("apple.awt.UIElement", "true");
		System.out.println("Starting TLC...");

		String path = args[0];
		ToolIO.reset();
		ToolIO.setMode(ToolIO.SYSTEM);
		ToolIO.setUserDir(path);

		String socket = args[1];
		// we are in a new jvm, so the handler is always null
		TLCMessageListener listener;
		if ("null".equals(socket)) {
			listener = null;
		} else if ("stdout".equals(socket)) {
			listener = new TLCMessageListener(TLCMessageHandler.printToStream(System.out));
		} else if ("stderr".equals(socket)) {
			listener = new TLCMessageListener(TLCMessageHandler.printToStream(System.err));
		} else {
			int port = Integer.parseInt(socket);
			Socket s = new Socket((String) null, port);
			listener = new TLCMessageListener(TLCMessageHandler.printToStream(s.getOutputStream()));
		}

		String[] parameters = new String[args.length - 2];
		System.arraycopy(args, 2, parameters, 0, parameters.length);
		try {
			if (listener != null) {
				listener.start();
			}
			TLC.main(parameters);
		} catch (Exception e) {
			throw new RuntimeException(e);
		} finally {
			if (listener != null) {
				listener.finish();
			}
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
		processBuilder.redirectErrorStream(true);
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

	public static void runTLCInANewJVM(String machineName, File path) throws IOException {
		List<String> list = buildTlcArgs(machineName);
		list.add(0, path.getPath()); // userdir must be first arg

		// socket must be second arg
		TLCSocketAcceptor socketAcceptor;
		if (handler != null) {
			ServerSocket s = new ServerSocket(0);
			list.add(1, String.valueOf(s.getLocalPort()));
			socketAcceptor = new TLCSocketAcceptor(s, handler);
		} else {
			list.add(1, "null");
			socketAcceptor = null;
		}

		final Process p = startJVM(TLCRunner.class.getCanonicalName(), list);
		StreamGobbler stdOut = new StreamGobbler(p.getInputStream());
		try {
			if (socketAcceptor != null) {
				socketAcceptor.start();
			}
			stdOut.start();
			p.waitFor();
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			if (socketAcceptor != null) {
				socketAcceptor.finish();
			}
		}
	}

	public static void runTLC(String machineName, File path) {
		StopWatch.start(MODEL_CHECKING_TIME);
		MP.printlnSilent("--------------------------------");
		MP.TLCOutputStream.changeOutputStream();
		ToolIO.reset();
		ToolIO.setMode(ToolIO.SYSTEM);
		ToolIO.setUserDir(path.getPath());

		TLCMessageListener listener;
		if (handler != null) {
			listener = new TLCMessageListener(handler);
		} else {
			listener = null;
		}

		String[] args = buildTlcArgs(machineName).toArray(new String[0]);
		TLC tlc = new TLC();
		// handle parameters
		if (tlc.handleParameters(args)) {
			tlc.setResolver(new SimpleFilenameToStream());
			// call the actual processing method
			try {
				if (listener != null) {
					listener.start();
				}
				tlc.process();
			} catch (Exception ignored) {
			} finally {
				if (listener != null) {
					listener.finish();
				}
			}
		}
		closeThreads();
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

	private static final class StreamGobbler extends Thread {

		private final InputStream is;
		private final ArrayList<String> log;

		public List<String> getLog() {
			return this.log;
		}

		StreamGobbler(InputStream is) {
			super("StreamGobbler for " + is);
			this.setDaemon(true);
			this.is = is;
			this.log = new ArrayList<>();
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
					this.log.add(line);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	private static final class TLCMessageListener extends Thread {

		private final TLCMessageHandler handler;
		private int lastMessageIndex = 0;

		public TLCMessageListener(TLCMessageHandler handler) {
			super("TLCMessageHandler");
			this.setDaemon(true);
			this.handler = handler;
		}

		@Override
		public void run() {
			try {
				while (!this.isInterrupted()) {
					List<Message> messages = TLC4BGlobals.getCurrentMessages();
					int count = messages.size();
					for (Message m : messages.subList(lastMessageIndex, count)) {
						if (m != null) {
							this.handler.onMessage(m);
						}
					}
					this.lastMessageIndex = count;
				}
			} catch (Exception e) {
				e.printStackTrace();
			} finally {
				try {
					this.handler.close();
				} catch (Exception ignored) {
				}
			}
		}

		public void finish() {
			this.interrupt();
		}
	}

	private static final class TLCSocketAcceptor extends Thread {

		private final ServerSocket serverSocket;
		private final TLCMessageHandler handler;
		private final List<TLCSocketConnection> connections = new ArrayList<>();

		private TLCSocketAcceptor(ServerSocket serverSocket, TLCMessageHandler handler) {
			super("TLCSocketAcceptor");
			this.setDaemon(true);
			this.serverSocket = serverSocket;
			this.handler = handler;
		}

		@Override
		public void run() {
			// we only accept a single connection, no loop!
			try {
				Socket socket = serverSocket.accept();
				TLCSocketConnection connection = new TLCSocketConnection(socket, this.handler);
				this.connections.add(connection);
				connection.start();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		public void finish() {
			this.interrupt();
			for (TLCSocketConnection connection : this.connections) {
				connection.finish();
			}
			this.connections.clear();
		}
	}

	private static final class TLCSocketConnection extends Thread {

		private final Socket socket;
		private final TLCMessageHandler handler;

		private TLCSocketConnection(Socket socket, TLCMessageHandler handler) {
			super("TLCSocketConnection-" + socket);
			this.setDaemon(true);
			this.socket = socket;
			this.handler = handler;
		}

		@Override
		public void run() {
			try {
				BufferedReader r = new BufferedReader(new InputStreamReader(socket.getInputStream()));
				String line;
				while (!this.isInterrupted() && (line = r.readLine()) != null) {
					Message message = TLCMessageHandler.fromLine(line);
					if (message != null) {
						this.handler.onMessage(message);
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			} finally {
				try {
					this.socket.close();
				} catch (Exception ignored) {
				}
			}
		}

		public void finish() {
			this.interrupt();
		}
	}
}
