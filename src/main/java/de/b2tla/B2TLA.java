package de.b2tla;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.Writer;
import java.util.ArrayList;
import de.b2tla.Globals;

import util.ToolIO;

import de.b2tla.analysis.UsedStandardModules;
import de.b2tla.analysis.UsedStandardModules.STANDARD_MODULES;
import de.be4.classicalb.core.parser.exceptions.BException;

public class B2TLA {

	private String mainFileName;
	private String machineName;
	private String pathAndName;
	private String path;
	private String tlaModule;
	private String config;
	B2TlaTranslator translator;

	public static void main(String[] args) throws IOException {

		B2TLA b2tla = new B2TLA();

		try {
			b2tla.progress(args);
		} catch (Exception e) {
			System.err.println(e.getMessage());
			return;
		}
		
		if (Globals.tool) {
			//ToolIO.setMode(ToolIO.TOOL);
		}
		if (Globals.runTLC) {
			TLCRunner.runtTLC(b2tla.machineName, b2tla.path);
		}
		System.exit(0);
	}
	
	public static void test(String[] args) throws IOException {
		//TODO raise Exception if it fails (TLC Error)
		B2TLA b2tla = new B2TLA();

		try {
			b2tla.progress(args);
		} catch (Exception e) {
			System.err.println(e.getMessage());
			return;
		}
		
		if (Globals.tool) {
			ToolIO.setMode(ToolIO.TOOL);
		}
		if (Globals.runTLC) {
			TLCRunner.runtTLC(b2tla.machineName, b2tla.path);
		}
	}

	private void handleParameter(String[] args) {
		int index = 0;
		while (index < args.length) {
			if (args[index].toLowerCase().equals("-nodead")) {
				Globals.deadlockCheck = false;
			} else if (args[index].toLowerCase().equals("-notlc")) {
				Globals.runTLC = false;
			} else if (args[index].toLowerCase().equals("-notranslation")) {
				Globals.translate = false;
			} else if (args[index].toLowerCase().equals("-nogoal")) {
				Globals.GOAL = false;
			} else if (args[index].toLowerCase().equals("-noinv")) {
				Globals.invariant = false;
			} else if (args[index].toLowerCase().equals("-tool")) {
				Globals.tool = true;
			} else if (args[index].charAt(0) == '-') {
				System.err
						.println("Error: unrecognized option: " + args[index]);
				System.exit(1);
			} else {
				if (mainFileName != null) {
					System.out.println("Error: more than one input files: "
							+ mainFileName + " and " + args[index]);
					System.exit(1);
				}
				mainFileName = args[index];
			}
			index++;
		}
		if (mainFileName == null) {
			System.out.println("Main machine required!");
			System.exit(1);
		}

	}

	private void progress(String[] args) throws IOException, BException {
		handleParameter(args);

		handleMainFileName();
		if (Globals.translate) {
			try {
				translator = new B2TlaTranslator(machineName, getFile());
				translator.translate();
			} catch (Exception e) {
				System.err.println(e.getMessage());
				//e.printStackTrace();
				System.exit(1);
			}

			this.tlaModule = translator.getModuleString();
			this.config = translator.getConfigString();
			createTlaFiles();
		}

	}

	private void handleMainFileName() {
		String name = mainFileName;
		name = name.replace("\\", File.separator);
		name = name.replace("/", File.separator);

		if (name.toLowerCase().endsWith(".mch")) {
			name = name.substring(0, name.length() - 4);
		}
		pathAndName = name;
		if (name.contains(File.separator)) {
			path = name.substring(0, name.lastIndexOf(File.separator) + 1);
		} else {
			path = "." + File.separator;
		}

		machineName = name.substring(name.lastIndexOf(File.separator) + 1);
	}

	private void createTlaFiles() {
		File tlaFile = new File(pathAndName + ".tla");
		try {
			tlaFile.createNewFile();
		} catch (IOException e) {
			e.printStackTrace();
		}

		try {
			Writer fw = new FileWriter(tlaFile);
			fw.write(tlaModule);
			fw.close();
			System.out.println("TLA Module '" + pathAndName + ".tla' created.");
		} catch (IOException e) {
			e.printStackTrace();
		}

		File configFile = new File(pathAndName + ".cfg");
		try {
			configFile.createNewFile();
		} catch (IOException e) {
			e.printStackTrace();
		}

		try {
			Writer fw = new FileWriter(configFile);
			fw.write(config);
			fw.close();
			System.out.println("Configuration file '" + pathAndName
					+ ".cfg' created.");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// createUsedStandardModules(path, translator.getUsedStandardModule());
		createModules(path, translator.getUsedStandardModule());
	}

	private void createModules(String path2,
			ArrayList<STANDARD_MODULES> usedStandardModule) {
		if (usedStandardModule.contains(STANDARD_MODULES.Relations)) {
			createStandardModule("Relations", path,
					translator.getUsedStandardModule());
		}
		if (usedStandardModule.contains(STANDARD_MODULES.BBuiltIns)) {
			createStandardModule("BBuiltIns", path,
					translator.getUsedStandardModule());
		}

	}

	private void createStandardModule(String name, String path,
			ArrayList<UsedStandardModules.STANDARD_MODULES> standardModules) {
		InputStream is = null;
		FileOutputStream fos = null;
		try {
			is = this.getClass().getClassLoader()
					.getResourceAsStream("standardModules/" + name + ".tla");
			if (is == null) {
				is = new FileInputStream("src/main/resources/standardModules/"
						+ name + ".tla");
			}

			fos = new FileOutputStream(path + name + ".tla");

			int read = 0;
			byte[] bytes = new byte[1024];

			while ((read = is.read(bytes)) != -1) {
				fos.write(bytes, 0, read);
			}

			System.out.println("Standard module '" + path + name
					+ ".tla' created.");
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				is.close();
				fos.flush();
				fos.close();
			} catch (IOException ex) {
				ex.printStackTrace();
			}
		}
	}

	public static void createUsedStandardModules(String path,
			ArrayList<UsedStandardModules.STANDARD_MODULES> standardModules) {
		if (standardModules.contains(STANDARD_MODULES.Relations)) {
			File naturalsFile = new File(path + File.separator
					+ "Relations.tla");
			if (!naturalsFile.exists()) {
				try {
					naturalsFile.createNewFile();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}

			try {
				Writer fw = new FileWriter(naturalsFile);
				fw.write(StandardModules.Relations);
				fw.close();
				System.out.println("Standard module '" + naturalsFile.getName()
						+ "' created.");
			} catch (IOException e) {
				e.printStackTrace();
			}

		}

		if (standardModules.contains(STANDARD_MODULES.BBuiltIns)) {
			File bBuiltInsFile = new File(path + File.separator
					+ "BBuiltIns.tla");
			if (!bBuiltInsFile.exists()) {
				try {
					bBuiltInsFile.createNewFile();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			try {
				Writer fw = new FileWriter(bBuiltInsFile);
				fw.write(StandardModules.BBuiltIns);
				fw.close();
				System.out.println("Standard modules BBuiltIns.tla created.");
			} catch (IOException e) {
				e.printStackTrace();
			}

		}

	}

	private File getFile() {
		File mainFile = new File(mainFileName);
		if (!mainFile.exists()) {
			throw new RuntimeException("The file " + mainFileName
					+ " does not exist.");
		}
		return mainFile;
	}

	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = in.readLine()) != null) {
			res.append(str + "\n");
		}
		in.close();
		return res.toString();
	}
}
