package de.b2tla.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;




import java.util.List;

import de.b2tla.Translator;
import de.b2tla.analysis.Ast2String;
import de.b2tla.tlc.TLCResults.TLCResult;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class TestUtil {

	public static void compare(String expectedModule, String machine)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());
		/**
		 * create standard modules BBuildins
		 */

		String name = b2tlaTranslator.getMachineName();
		StringBuilder sb1 = de.tla2b.translation.Tla2BTranslator
				.translateString(name, b2tlaTranslator.getModuleString(), null);
		StringBuilder sb2 = de.tla2b.translation.Tla2BTranslator
				.translateString(name, expectedModule, null);
		if (!sb2.toString().equals(sb1.toString())) {
			// assertEquals(expected, actual);

			fail("expected:\n" + expectedModule + "\nbut was:\n"
					+ b2tlaTranslator.getModuleString());
		}
		// assertEquals(sb2.toString(), sb1.toString());
	}
	
	
	public static void compareLTL(String expectedModule, String machine, String ltlFormula)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine, ltlFormula);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());
		String name = b2tlaTranslator.getMachineName();
		de.tla2b.translation.Tla2BTranslator
		.translateString(name, b2tlaTranslator.getModuleString(), null);
		assertEquals(expectedModule, b2tlaTranslator.getModuleString());
	}
	
	public static void checkMachine(String machine)
			throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());

		String name = b2tlaTranslator.getMachineName();
		de.tla2b.translation.Tla2BTranslator
				.translateString(name, b2tlaTranslator.getModuleString(), null);
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
		de.tla2b.translation.Tla2BTranslator
				.translateString(name, b2tlaTranslator.getModuleString(),
						b2tlaTranslator.getConfigString());
		
		assertEquals(expectedModule, b2tlaTranslator.getModuleString());
		assertEquals(expectedConfig, b2tlaTranslator.getConfigString());
	}
	
	public static void compareConfig(String expectedModule,
			String expectedConfig, String machine) throws Exception {
		Translator b2tlaTranslator = new Translator(machine);
		b2tlaTranslator.translate();
		// print(b2tlaTranslator.getStart());
		System.out.println(b2tlaTranslator.getModuleString());
		System.out.println(b2tlaTranslator.getConfigString());

		String name = b2tlaTranslator.getMachineName();
		StringBuilder sb1 = de.tla2b.translation.Tla2BTranslator
				.translateString(name, b2tlaTranslator.getModuleString(),
						b2tlaTranslator.getConfigString());
		StringBuilder sb2 = de.tla2b.translation.Tla2BTranslator
				.translateString(name, expectedModule, expectedConfig);
		if (!sb2.toString().equals(sb1.toString())) {
			fail("expected:\n" + expectedModule + "\nbut was:\n"
					+ b2tlaTranslator.getModuleString() + "\n\nexpected:\n"
					+ expectedConfig + "\nbut was:\n"
					+ b2tlaTranslator.getConfigString());
		}
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

	public static void createTempfile(String dir, String fileName,
			String moduleString) {
		File d = new File(dir);
		d.mkdirs();

		File tempFile = new File(dir + fileName);
		try {
			tempFile.createNewFile();
			System.out
					.println("Testfile:'" + tempFile.getName() + "' created.");
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		FileWriter fw;
		try {
			fw = new FileWriter(tempFile);
			fw.write(moduleString);
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	
	public static TLCResult test(String[] args) throws IOException {
		System.out.println("Starting JVM...");
		final Process p = startJVM("", TLC4BTester.class.getCanonicalName(), args);
		StreamGobbler stdOut = new StreamGobbler(p.getInputStream());
		stdOut.start();
		StreamGobbler errOut = new StreamGobbler(p.getErrorStream());
		errOut.start();
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		for (int i = stdOut.getLog().size()-1; i > 1 ; i--) {
			String s = stdOut.getLog().get(i);
			//System.out.println(s);
			if(s.startsWith("Result:")){
				String resultString = s.substring(s.indexOf(':') + 2);
				resultString = resultString.replaceAll("\\s+","");
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
			InputStreamReader isr = new InputStreamReader(is);
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

