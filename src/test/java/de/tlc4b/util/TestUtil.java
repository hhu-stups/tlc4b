package de.tlc4b.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.tla2b.exceptions.TLA2BException;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.Translator;
import de.tlc4b.tlc.TLCResults.TLCResult;

import util.ToolIO;

import static de.tlc4b.TLC4BOption.NOTRACE;
import static org.junit.Assert.assertEquals;

public class TestUtil {
	private static final String MCH_SUFFIX = ".mch";

	public static File[] getMachines(String path) {
		return new File(path).listFiles((dir, name) -> name.endsWith(MCH_SUFFIX));
	}

	public static List<File> getMachinesRecursively(String path) {
		File root = new File(path);
		File[] list = root.listFiles();

		List<File> files = new ArrayList<>();
		if (list == null) {
			return files;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				files.addAll(getMachinesRecursively(f.getAbsolutePath()));
			} else {
				String name = f.getName();
				if (name.endsWith(MCH_SUFFIX)) {
					files.add(f);
				}
			}
		}

		return files;
	}

	public static void compare(final String expectedModule, final String machineString) throws BCompoundException, TLA2BException {
		TLC4BGlobals.setForceTLCToEvalConstants(false);
		ToolIO.setMode(ToolIO.TOOL);

		Translator b2tlaTranslator = new Translator(machineString);
		b2tlaTranslator.translate();
		System.out.println("Input B machine:");
		System.out.println(machineString);
		System.out.println("Expected TLA+ module:");
		System.out.println(expectedModule);
		System.out.println("Translated TLA+ module:");
		System.out.println(b2tlaTranslator.getModuleString());

		// TODO create standard modules BBuildins

		String moduleName = b2tlaTranslator.getMachineName();
		String actualB = de.tla2bAst.Translator.translateModuleString(moduleName, b2tlaTranslator.getModuleString(), b2tlaTranslator.getConfigString());
		String expectedB = de.tla2bAst.Translator.translateModuleString(moduleName, expectedModule, b2tlaTranslator.getConfigString());
		if (!expectedB.equals(actualB)) {
			System.out.println("Expected TLA+ module translated to B machine:");
			System.out.println(expectedB);
			System.out.println("Actual translated TLA+ module translated back to B machine:");
			System.out.println(actualB);
		}
		assertEquals(expectedB, actualB);
	}

	public static String translateTLA2B(String moduleName, String tlaString, String configString)
			throws TLA2BException {
		return de.tla2bAst.Translator.translateModuleString(moduleName, tlaString, configString);
	}

	public static void compareLTLFormula(String expected, String machine, String ltlFormula) throws BCompoundException {
		Translator b2tlaTranslator = new Translator(machine, ltlFormula);
		b2tlaTranslator.translate();
		String translatedLTLFormula = b2tlaTranslator.getTranslatedLTLFormula();
		translatedLTLFormula = translatedLTLFormula.replaceAll("\\s", "");
		expected = expected.replaceAll("\\s", "");
		assertEquals(expected, translatedLTLFormula);
	}

	public static void checkMachine(String machine) throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();

		String name = b2tlaTranslator.getMachineName();
		translateTLA2B(name, b2tlaTranslator.getModuleString(), b2tlaTranslator.getConfigString());
		// TODO Check that re-translated B machine matches original input?
	}

	public static void compareModuleAndConfig(String expectedModule, String expectedConfig, String machine)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();

		assertEquals(expectedModule, b2tlaTranslator.getModuleString());
		assertEquals(expectedConfig, b2tlaTranslator.getConfigString());

		String name = b2tlaTranslator.getMachineName();

		// parse check
		translateTLA2B(name, b2tlaTranslator.getModuleString(), b2tlaTranslator.getConfigString());
		// TODO Check that re-translated B machine matches original input?
	}

	public static String translate(String machine) throws BCompoundException {
		Translator translator = new Translator(machine);
		translator.translate();
		return translator.getModuleString();
	}

	public static TLCResult testString(String machineString) throws IOException {
		String runnerClassName = TLC4BRunnerTestString.class.getCanonicalName();
		String[] args = new String[] { machineString };
		return runTLC(runnerClassName, args);
	}

	public static TLCResult test(String[] args) throws IOException {
		String[] newArgs = Arrays.copyOf(args, args.length + 1);
		newArgs[args.length] = NOTRACE.cliArg();
		String runnerClassName = TLC4BTester.class.getCanonicalName();
		return runTLC(runnerClassName, newArgs);
	}

	public static TLCResult testWithTrace(String[] args) throws IOException {
		String runnerClassName = TLC4BTester.class.getCanonicalName();
		return runTLC(runnerClassName, args);
	}

	private static TLCResult runTLC(String runnerClassName, String[] args) throws IOException {
		final Process p = startJVM(runnerClassName, args);
		StreamGobbler stdOut = new StreamGobbler(p.getInputStream());
		stdOut.start();
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		for (int i = stdOut.getLog().size() - 1; i > 1; i--) {
			String s = stdOut.getLog().get(i);
			if (s.startsWith("Result:")) {
				String resultString = s.substring(s.indexOf(':') + 2);
				resultString = resultString.replaceAll("\\s+", "");
				return TLCResult.valueOf(resultString);
			}
		}
		return null;

	}

	private static Process startJVM(final String mainClass, final String[] arguments)
			throws IOException {

		String separator = FileSystems.getDefault().getSeparator();

		String jvm = System.getProperty("java.home") + separator + "bin" + separator + "java";
		String classpath = System.getProperty("java.class.path");

		List<String> command = new ArrayList<>();
		command.add(jvm);
		command.add("-cp");
		command.add(classpath);
		command.add(mainClass);
		command.addAll(Arrays.asList(arguments));

		ProcessBuilder processBuilder = new ProcessBuilder(command);
		processBuilder.redirectErrorStream(true);
		return processBuilder.start();
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
