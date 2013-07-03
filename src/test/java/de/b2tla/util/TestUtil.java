package de.b2tla.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Hashtable;

import util.ToolIO;

import de.b2tla.B2TLA;
import de.b2tla.B2TlaTranslator;
import de.b2tla.analysis.Ast2String;
import de.b2tla.btypes.BType;
import de.b2tla.tlc.TLCExpressionParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.translation.TLA2B;

public class TestUtil {

	public static void compare(String expectedModule, String machine)
			throws Exception {
		B2TlaTranslator b2tlaTranslator = new B2TlaTranslator(machine);
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
	
	public static void checkMachine(String machine)
			throws Exception {
		B2TlaTranslator b2tlaTranslator = new B2TlaTranslator(machine);
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

	public static void compareConfig(String expectedModule,
			String expectedConfig, String machine) throws Exception {
		B2TlaTranslator b2tlaTranslator = new B2TlaTranslator(machine);
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
		B2TlaTranslator b2tlaTranslator = new B2TlaTranslator(machine);
		b2tlaTranslator.translate();
		System.out.println(b2tlaTranslator.getModuleString());
		assertEquals(expected, b2tlaTranslator.getModuleString());
	}

	public static String translate(String machine) throws BException {
		B2TlaTranslator translator = new B2TlaTranslator(machine);
		translator.translate();
		System.out.println(translator.getModuleString());
		return translator.getModuleString();
	}

	public static void compare2(String expected, String machine)
			throws Exception {
		B2TlaTranslator b2tlaTranslator = new B2TlaTranslator(machine);
		b2tlaTranslator.translate();
		String name = b2tlaTranslator.getMachineName();
		String module = b2tlaTranslator.getModuleString();

		String dir = "build/testfiles/";
		createTempfile(dir, name + ".tla", module);

		B2TLA.createUsedStandardModules(dir,
				b2tlaTranslator.getUsedStandardModule());
		ToolIO.setMode(ToolIO.TOOL);
		String sb1 = TLA2B.translateFile(dir + name);
		// result
		createTempfile(dir, name + ".tla", expected);
		String sb2 = TLA2B.translateFile(dir + name);

		if (!sb2.toString().equals(sb1)) {
			// assertEquals(expected, actual);
			fail("expected:\n" + expected + "\nbut was:\n" + module);
		}
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

	public static void compareExpr(String expected, String tla) {
		String res = TLCExpressionParser.parseLine(tla);
		System.out.println(res);
		res = res.replaceAll("\\s", "");
		expected = expected.replaceAll("\\s", "");
		assertEquals(expected, res);
	}

	public static void compareExpr(String expected, String tla,
			Hashtable<String, BType> types) {
		String res = TLCExpressionParser.parseLine(tla, types);
		System.out.println(res);
		res = res.replaceAll("\\s", "");
		expected = expected.replaceAll("\\s", "");
		assertEquals(expected, res);
	}

}
