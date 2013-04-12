package de.b2tla;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;

import de.b2tla.util.MyPrintStream;

import util.SimpleFilenameToStream;
import util.ToolIO;
import tlc2.TLC;

public class TLCRunner {

	public static void runtTLC(String machineName, String path) {
		ArrayList<String> list = new ArrayList<String>();
		if (!Globals.deadlockCheck) {
			list.add("-deadlock");
		}
		list.add(machineName);
		ToolIO.setUserDir(path);
		String[] args = list.toArray(new String[list.size()]);

		// ByteArrayOutputStream os = new ByteArrayOutputStream();
		// PrintStream ps = new PrintStream(os);
		MyPrintStream myStream = new MyPrintStream();
		PrintStream old = System.out;
		System.setOut(myStream);
		ToolIO.setMode(ToolIO.SYSTEM);

		TLC tlc = new TLC();
		// handle parameters
		if (tlc.handleParameters(args)) {
			tlc.setResolver(new SimpleFilenameToStream());
			// call the actual processing method
			tlc.process();
		}
		System.setOut(old);
		
		// System.out.println("'"+output+"'");
		// if (Globals.tool) {
		//String[] messages = ToolIO.getAllMessages();
		String[] messages = myStream.getArray();
		TLCOutputEvaluator evaluator = new TLCOutputEvaluator(machineName,
				messages);
		StringBuilder trace = evaluator.getTrace();
		if (trace != null) {
			createfile(path, machineName + ".tla.trace", trace.toString());
		}
		// String res = "";
		// for (int i = 0; i < messages.length; i++) {
		// res += messages[i] + "\n";
		// }
		// System.out.println(res);
		// createfile(path, machineName + ".tla.temp", res);
		// here are no informations about TLCs work
		// }
		// terminate
	}

	public static void createfile(String dir, String fileName, String text) {
		File d = new File(dir);
		d.mkdirs();
		File tempFile = new File(dir + File.separator + fileName);
		try {
			tempFile.createNewFile();
			System.out
					.println("Tempfile:'" + tempFile.getName() + "' created.");
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		FileWriter fw;
		try {
			fw = new FileWriter(tempFile);
			fw.write(text);
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
