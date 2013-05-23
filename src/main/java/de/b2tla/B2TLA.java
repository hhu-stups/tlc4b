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
import java.util.HashSet;
import java.util.Set;

import de.b2tla.Globals;

import tla2tex.FindAlignments;
import util.ToolIO;

import de.b2tla.analysis.UsedStandardModules;
import de.b2tla.analysis.UsedStandardModules.STANDARD_MODULES;
import de.b2tla.exceptions.B2tlaException;
import de.b2tla.tlc.TLCOutput;
import de.b2tla.tlc.TLCOutput.ERROR;
import de.b2tla.util.StopWatch;
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
		StopWatch.start("Translation");
		B2TLA b2tla = new B2TLA();

		try {
			b2tla.progress(args);
		} catch (Exception e) {
			System.err.println(e.getMessage());
			return;
		}
		StopWatch.stop("Translation");
		if (Globals.runTLC) {
			ArrayList<String> output = TLCRunner.runTLCInANewJVM(
					b2tla.machineName, b2tla.path);
			b2tla.evalOutput(output, false);

		}

	}

	public static ERROR test(String[] args) throws IOException {
		B2TLA b2tla = new B2TLA();
		try {
			b2tla.progress(args);
		} catch (Exception e) {
			e.printStackTrace();
			System.err.println(e.getMessage());
			return null;
		}

		if (Globals.runTLC) {
			ArrayList<String> output = TLCRunner.runTLCInANewJVM(
					b2tla.machineName, b2tla.path);
			ERROR error = TLCOutput.findError(output);
			System.out.println(error);
			return error;
		}
		return null;
	}

	private void evalOutput(ArrayList<String> output, boolean createTraceFile) {
		TLCOutput tlcOutput = new TLCOutput(machineName,
				output.toArray(new String[output.size()]));
		tlcOutput.parseTLCOutput();
		System.out.println("ERROR: " + tlcOutput.getError());
		StringBuilder trace = tlcOutput.getErrorTrace();
		if (tlcOutput.hasTrace() && createTraceFile) {
			String tracefileName = machineName + ".tla.trace";
			createFile(path, tracefileName, trace.toString(), "Trace file '"
					+ path + tracefileName + "'created.", true);
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
				throw new B2tlaException("Error: unrecognized option: "
						+ args[index]);
			} else {
				if (mainFileName != null) {
					throw new B2tlaException(
							"Error: more than one input files: " + mainFileName
									+ " and " + args[index]);
				}
				mainFileName = args[index];
				
			}
			index++;
		}
		if (mainFileName == null) {
			throw new B2tlaException("Main machine required!");
		}
	}

	private void progress(String[] args) throws IOException, BException {
		handleParameter(args);

		handleMainFileName();
		if (Globals.translate) {
			translator = new B2TlaTranslator(machineName, getFile());
			translator.translate();

			this.tlaModule = translator.getModuleString();
			this.config = translator.getConfigString();
			createFiles();
		}

	}

	private void handleMainFileName() {
		String name = mainFileName;
		name = name.replace("\\", File.separator);
		name = name.replace("/", File.separator);

		mainFileName = name;
		
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

	private void createFiles() {
		createFile(path, machineName + ".tla", tlaModule, "TLA+ module '"
				+ pathAndName + ".tla' created.", Globals.deleteOnExit);
		createFile(path, machineName + ".cfg", config, "Configuration file '"
				+ pathAndName + ".cfg' created.", Globals.deleteOnExit);

		createStandardModules();
	}

	private void createStandardModules() {
		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.Relations)) {
			createStandardModule(path, STANDARD_MODULES.Relations.toString());
		}
		
		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.Functions)) {
			createStandardModule(path, STANDARD_MODULES.Functions.toString());
		}
		
		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.FunctionsAsRelations)) {
			createStandardModule(path, STANDARD_MODULES.FunctionsAsRelations.toString());
			if (!translator.getUsedStandardModule().contains(
					STANDARD_MODULES.Functions)) {
				createStandardModule(path, STANDARD_MODULES.Functions.toString());
			}
		}
	
		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.SequencesExtended)) {
			createStandardModule(path, STANDARD_MODULES.SequencesExtended.toString());
		}
		
		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.SequencesAsRelations)) {
			createStandardModule(path, STANDARD_MODULES.SequencesAsRelations.toString());
		}
	}

	private void createStandardModule(String path, String name) {
		// standard modules are copied from the standardModules folder to the
		// current directory
		
		File file = new File(path + name + ".tla");
		InputStream is = null;
		FileOutputStream fos = null;
		try {
			is = this.getClass().getClassLoader()
					.getResourceAsStream("standardModules/" + name + ".tla");
			if (is == null) {
				is = new FileInputStream("src/main/resources/standardModules/"
						+ name + ".tla");
			}

			fos = new FileOutputStream(file);

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
			if(Globals.deleteOnExit){
				file.deleteOnExit();
			}
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
			throw new B2tlaException("The file " + mainFileName
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

	public static void createFile(String dir, String fileName, String text,
			String message, boolean deleteOnExit) {
		File d = new File(dir);
		d.mkdirs();
		File file = new File(dir + File.separator + fileName);
		try {
			file.createNewFile();
			FileWriter fw;
			fw = new FileWriter(file);
			fw.write(text);
			fw.close();
			System.out.println(message);
		} catch (IOException e) {
			e.printStackTrace();
			throw new B2tlaException(e.getMessage());
		} finally {
			if (deleteOnExit) {
				file.deleteOnExit();
			}
		}
	}

}
