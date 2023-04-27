package de.tlc4b.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.tla2b.exceptions.TLA2BException;
import de.tlc4b.TLC4B;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.Translator;
import de.tlc4b.tlc.TLCResults.TLCResult;

import util.ToolIO;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class TestUtil {

	public static void compare(final String expectedModule, final String machineString) throws Exception {
		TLC4BGlobals.setForceTLCToEvalConstants(false);
		ToolIO.setMode(ToolIO.TOOL);

		Translator b2tlaTranslator = new Translator(machineString);
		b2tlaTranslator.translate();

		// TODO create standard modules BBuildins

		String moduleName = b2tlaTranslator.getMachineName();
		String str1 = de.tla2bAst.Translator.translateModuleString(moduleName, b2tlaTranslator.getModuleString(), null);

		String str2 = de.tla2bAst.Translator.translateModuleString(moduleName, expectedModule, null);
		// StringBuilder sb1 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, b2tlaTranslator.getModuleString(), null);
		// StringBuilder sb2 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, expectedModule, null);
		if (!str1.equals(str2)) {
			// assertEquals(expected, actual);

			fail("expected:\n" + expectedModule + "\nbut was:\n" + b2tlaTranslator.getModuleString());
		}
		// assertEquals(sb2.toString(), sb1.toString());
	}

	public static void tryTranslating(final String machineString) throws BException {
		TLC4BGlobals.setForceTLCToEvalConstants(false);
		ToolIO.setMode(ToolIO.TOOL);
		Translator b2tlaTranslator;
		try {
			b2tlaTranslator = new Translator(machineString);
			b2tlaTranslator.translate();
		} catch (BCompoundException e) {
			throw e.getFirstException();
		}

	}

	public static String translateTLA2B(String moduleName, String tlaString) throws TLA2BException {
		return de.tla2bAst.Translator.translateModuleString(moduleName, tlaString, null);
	}

	public static String translateTLA2B(String moduleName, String tlaString, String configString)
			throws TLA2BException {
		return de.tla2bAst.Translator.translateModuleString(moduleName, tlaString, configString);
	}

	public static void compareLTLFormula(String expected, String machine, String ltlFormula) throws Exception {
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
		translateTLA2B(name, b2tlaTranslator.getModuleString());
		// de.tla2b.translation.Tla2BTranslator.translateString(name,
		// b2tlaTranslator.getModuleString(), null);
	}

	public static void compareEqualsConfig(String expectedModule, String expectedConfig, String machine)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();

		String name = b2tlaTranslator.getMachineName();

		// parse check
		translateTLA2B(name, b2tlaTranslator.getModuleString(), b2tlaTranslator.getConfigString());

		assertEquals(expectedModule, b2tlaTranslator.getModuleString());
		assertEquals(expectedConfig, b2tlaTranslator.getConfigString());
	}

	public static void compareModuleAndConfig(String expectedModule, String expectedConfig, String machine)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();

		// TODO include config file in back translation from TLA+ to B

		// String name = b2tlaTranslator.getMachineName();
		// StringBuilder sb1 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, b2tlaTranslator.getModuleString(),
		// b2tlaTranslator.getConfigString());
		// StringBuilder sb2 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, expectedModule, expectedConfig);
		// if (!sb2.toString().equals(sb1.toString())) {
		// fail("expected:\n" + expectedModule + "\nbut was:\n"
		// + b2tlaTranslator.getModuleString() + "\n\nexpected:\n"
		// + expectedConfig + "\nbut was:\n"
		// + b2tlaTranslator.getConfigString());
		// }
	}

	public static void compareEquals(String expected, String machine) throws BException {
		try {
			Translator b2tlaTranslator = new Translator(machine);
			b2tlaTranslator.translate();
			assertEquals(expected, b2tlaTranslator.getModuleString());
		} catch (BCompoundException e) {
			throw e.getFirstException();
		}

	}

	public static String translate(String machine) throws BException {
		try {
			Translator translator = new Translator(machine);
			translator.translate();
			return translator.getModuleString();
		} catch (BCompoundException e) {
			throw e.getFirstException();
		}
	}

	public static TLCResult testString(String machineString) throws IOException {
		String runnerClassName = TLC4BRunnerTestString.class.getCanonicalName();
		String[] args = new String[] { machineString };
		return runTLC(runnerClassName, args);
	}

	public static TLCResult test(String[] args) throws IOException {
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

		String separator = System.getProperty("file.separator");

		String jvm = System.getProperty("java.home") + separator + "bin" + separator + "java";
		String classpath = System.getProperty("java.class.path");

		List<String> command = new ArrayList<String>();
		command.add(jvm);
		command.add("-cp");
		command.add(classpath);
		command.add(mainClass);
		command.addAll(Arrays.asList(arguments));

		ProcessBuilder processBuilder = new ProcessBuilder(command);
		processBuilder.redirectErrorStream(true);
		Process process = processBuilder.start();
		return process;
	}

	public static void testParse(String[] args, boolean deleteFiles) throws Exception {
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4BGlobals.setCreateTraceFile(false);
		TLC4BGlobals.setTestingMode(true);
		// B2TLAGlobals.setCleanup(true);
		TLC4B tlc4b = new TLC4B();
		try {
			tlc4b.process(args);
		} catch (Exception e) {
			e.printStackTrace();
			throw e;
		}
		File module = new File(tlc4b.getBuildDir(), tlc4b.getMachineFileNameWithoutFileExtension() + ".tla");

		// parse result
		new de.tla2bAst.Translator(module.getCanonicalPath());
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
