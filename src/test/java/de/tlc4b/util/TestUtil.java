package de.tlc4b.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import util.ToolIO;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.exceptions.TLA2BException;
import de.tlc4b.TLC4B;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.Translator;
import de.tlc4b.tlc.TLCResults.TLCResult;

public class TestUtil {

	public static void compare(String expectedModule, String machine)
			throws Exception {
		TLC4BGlobals.setForceTLCToEvalConstants(false);
		ToolIO.setMode(ToolIO.TOOL);

		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());
		
		//TODO  create standard modules BBuildins
		 

		String moduleName = b2tlaTranslator.getMachineName();
		String str1 = translateTLA2B(moduleName,
				b2tlaTranslator.getModuleString());

		String str2 = translateTLA2B(moduleName, expectedModule);
		// StringBuilder sb1 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, b2tlaTranslator.getModuleString(), null);
		// StringBuilder sb2 = de.tla2b.translation.Tla2BTranslator
		// .translateString(name, expectedModule, null);
		if (!str1.equals(str2)) {
			// assertEquals(expected, actual);

			fail("expected:\n" + expectedModule + "\nbut was:\n"
					+ b2tlaTranslator.getModuleString());
		}
		// assertEquals(sb2.toString(), sb1.toString());
	}

	public static String translateTLA2B(String moduleName, String tlaString)
			throws TLA2BException {
		return de.tla2bAst.Translator.translateModuleString(moduleName,
				tlaString, null);
	}

	public static String translateTLA2B(String moduleName, String tlaString,
			String configString) throws TLA2BException {
		return de.tla2bAst.Translator.translateModuleString(moduleName,
				tlaString, configString);
	}


	public static void compareLTLFormula(String expected, String machine,
			String ltlFormula) throws Exception {
		Translator b2tlaTranslator = new Translator(machine, ltlFormula);
		b2tlaTranslator.translate();
		String translatedLTLFormula = b2tlaTranslator.getTranslatedLTLFormula();
		translatedLTLFormula = translatedLTLFormula.replaceAll("\\s", "");
		expected = expected.replaceAll("\\s", "");
		System.out.println(translatedLTLFormula);
		System.out.println(b2tlaTranslator.getModuleString());
		assertEquals(expected, translatedLTLFormula);
	}

	public static void checkMachine(String machine) throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());

		String name = b2tlaTranslator.getMachineName();
		translateTLA2B(name, b2tlaTranslator.getModuleString());
		// de.tla2b.translation.Tla2BTranslator.translateString(name,
		// b2tlaTranslator.getModuleString(), null);
	}

	public static void print(Start start) {
		final Ast2String ast2String2 = new Ast2String();
		start.apply(ast2String2);
		System.out.println(ast2String2.toString());
	}

	public static void compareEqualsConfig(String expectedModule,
			String expectedConfig, String machine) throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		// print(b2tlaTranslator.getStart());
		System.out.println(b2tlaTranslator.getModuleString());
		System.out.println(b2tlaTranslator.getConfigString());

		String name = b2tlaTranslator.getMachineName();

		// parse check
		translateTLA2B(name, b2tlaTranslator.getModuleString(),
				b2tlaTranslator.getConfigString());

		assertEquals(expectedModule, b2tlaTranslator.getModuleString());
		assertEquals(expectedConfig, b2tlaTranslator.getConfigString());
	}

	public static void compareModuleAndConfig(String expectedModule,
			String expectedConfig, String machine) throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		// print(b2tlaTranslator.getStart());
		System.out.println(b2tlaTranslator.getModuleString());
		System.out.println(b2tlaTranslator.getConfigString());

		
		//TODO include config file in back translation from TLA+ to B
		
		
		
		
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

	public static void compareEquals(String expected, String machine)
			throws BException {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());
		assertEquals(expected, b2tlaTranslator.getModuleString());
	}

	public static String translate(String machine) throws BException {
		Translator translator = new Translator(machine);
		translator.translate();
		System.out.println(translator.getModuleString());
		return translator.getModuleString();
	}

	public static TLCResult test(String[] args) throws IOException {
		System.out.println("Starting JVM...");
		final Process p = startJVM("", TLC4BTester.class.getCanonicalName(),
				args);
		StreamGobbler stdOut = new StreamGobbler(p.getInputStream());
		stdOut.start();
		StreamGobbler errOut = new StreamGobbler(p.getErrorStream());
		errOut.start();
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		for (int i = stdOut.getLog().size() - 1; i > 1; i--) {
			String s = stdOut.getLog().get(i);
			// System.out.println(s);
			if (s.startsWith("Result:")) {
				String resultString = s.substring(s.indexOf(':') + 2);
				resultString = resultString.replaceAll("\\s+", "");
				System.out.println(resultString);
				return TLCResult.valueOf(resultString);
			}
		}
		System.out.println("No result found.");
		return null;
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

	public static void testParse(String[] args, boolean deleteFiles)
			throws Exception {
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
			System.err.println(e.getMessage());
			throw e;
		}
		File module = new File(tlc4b.getBuildDir(),
				tlc4b.getMachineFileNameWithoutFileExtension() + ".tla");

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
