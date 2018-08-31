package de.tlc4b;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.exceptions.TLC4BException;
import de.tlc4b.exceptions.TranslationException;
import de.tlc4b.tlc.TLCOutputInfo;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;
import static de.tlc4b.util.StopWatch.Watches.*;
import static de.tlc4b.MP.*;

public class TLC4B {

	private String filename;
	private File mainfile;
	private String machineFileNameWithoutFileExtension;
	// e.g. Test of file foo/bar/Test.mch
	private String logFileString;

	private File buildDir;

	private String tlaModule;
	private String config;
	private Translator translator;
	private TLCOutputInfo tlcOutputInfo;
	private String ltlFormula;
	private String constantsSetup;

	public static void main(String[] args) {
		System.setProperty("apple.awt.UIElement", "true");
		// avoiding pop up window

		TLC4B tlc4b = new TLC4B();
		try {
			tlc4b.process(args);
		} catch (BCompoundException e) {
			printlnErr("***** Parsing Error *****");
			printlnErr(e.getMessage());
			return;
		} catch (TLC4BException e) {
			printlnErr(e.getMessage());
			println("Model checking time: 0 sec");
			println("Result: " + e.getError());
			return;
		} catch (IOException e) {
			printlnErr(e.getMessage());
			println("Model checking time: 0 sec");
			println("Result: " + "I/O Error");
		}

		if (TLC4BGlobals.isRunTLC()) {
			try {

				TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension,
						tlc4b.buildDir);
				TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
				results.evalResults();
				tlc4b.printResults(results, TLC4BGlobals.isCreateTraceFile());
				Log log = new Log(tlc4b, results);
				tlc4b.createLogFile(log);
				System.exit(0);

			} catch (NoClassDefFoundError e) {
				printlnErr("Can not find TLC. The tlatools.jar must be included in the classpath.");
			}

		}

	}

	private void printResults(TLCResults results, boolean createTraceFile) {
		printOperationsCount(results);
		// options
		println("Used Options");
		println("| Number of workers: " + TLC4BGlobals.getWorkers());
		println("| Invariants check: " + TLC4BGlobals.isInvariant());
		println("| Deadlock check: " + TLC4BGlobals.isDeadlockCheck());
		println("| Assertion check: " + TLC4BGlobals.isAssertion());
		println("| Find Goal check: " + TLC4BGlobals.isGOAL());
		println("| LTL formulas check: " + TLC4BGlobals.isCheckLTL());
		println("| Partial invariant evaluation: "
				+ TLC4BGlobals.isPartialInvariantEvaluation());
		println("| Lazy constants setup: "
				+ !TLC4BGlobals.isForceTLCToEvalConstants());
		println("| Agressive well-definedness check: "
				+ TLC4BGlobals.checkWelldefinedness());
		println("| Prob constant setup: " + TLC4BGlobals.isProBconstantsSetup());
		println("| Symmetry reduction: " + TLC4BGlobals.useSymmetry());
		println("| MIN Int: " + TLC4BGlobals.getMIN_INT());
		println("| MAX Int: " + TLC4BGlobals.getMAX_INT());
		println("| Standard deferret set size: "
				+ TLC4BGlobals.getDEFERRED_SET_SIZE());
		println("--------------------------------");
		println("Parsing time: " + StopWatch.getRunTime(PARSING_TIME) + " ms");
		println("Translation time: " + StopWatch.getRunTime(TRANSLATION_TIME)
				+ " ms");
		println("Model checking time: " + results.getModelCheckingTime()
				+ " sec");
		// MP.printMessage("Number of workers: " +
		// TLCGlobals.getNumWorkers());
		if (results.getViolatedAssertions().size() > 0) {
			println("Violated assertions: " + results.getViolatedAssertions());
		}
		println("States analysed: " + results.getNumberOfDistinctStates());
		println("Transitions fired: " + results.getNumberOfTransitions());
		println("Result: " + results.getResultString());
		String violatedDefinition = results.getViolatedDefinition();
		if (violatedDefinition != null) {
			println("Violated Definition: " + violatedDefinition);
		}

		if (results.hasTrace() && createTraceFile) {
			String trace = results.getTrace();
			String tracefileName = machineFileNameWithoutFileExtension
					+ ".tla.trace";
			File traceFile = createFile(mainfile.getParentFile(),
					tracefileName, trace, false);
			if (traceFile != null) {
				println("Trace file '" + traceFile.getAbsolutePath()
						+ "' created.");
			}
		}

	}

	private void printOperationsCount(TLCResults results) {
		LinkedHashMap<String, Long> operationCount = results
				.getOperationCount();
		if (TLC4BGlobals.isPrintCoverage() && operationCount != null) {
			println("---------- Coverage statistics ----------");

			for (Entry<String, Long> entry : operationCount.entrySet()) {
				String key = entry.getKey();
				String value = entry.getValue().toString();
				println(key + ": " + value);
			}
			println("---------- End of coverage statistics ----------");
		}
	}

	public static void test(String[] args, boolean deleteFiles)
			throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up
															// windows
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
			printlnErr(e.getMessage());
			throw e;
		}
		if (TLC4BGlobals.isRunTLC()) {
			MP.TLCOutputStream.changeOutputStream();
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension,
					tlc4b.buildDir);
			MP.TLCOutputStream.resetOutputStream();
			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			tlc4b.printResults(results, false);

			System.exit(0);
		}
	}

	public static void testString(String machineString, boolean deleteFiles)
			throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up
															// windows
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4BGlobals.setCreateTraceFile(false);
		TLC4BGlobals.setTestingMode(true);
		// B2TLAGlobals.setCleanup(true);
		TLC4B tlc4b = new TLC4B();
		tlc4b.buildDir = new File("temp/");

		tlc4b.machineFileNameWithoutFileExtension = "Test";

		StopWatch.start(PARSING_TIME);
		MP.print("Parsing... ");
		tlc4b.translator = new Translator(machineString);
		StopWatch.stop(PARSING_TIME);
		println("(" + StopWatch.getRunTimeAsString(PARSING_TIME) + "ms)");

		StopWatch.start(TRANSLATION_TIME);
		MP.print("Translating... ");
		tlc4b.translator.translate();
		tlc4b.tlaModule = tlc4b.translator.getModuleString();
		tlc4b.config = tlc4b.translator.getConfigString();
		tlc4b.tlcOutputInfo = tlc4b.translator.getTLCOutputInfo();
		StopWatch.stop(TRANSLATION_TIME);
		println("(" + StopWatch.getRunTimeAsString(TRANSLATION_TIME) + "ms)");
		tlc4b.createFiles();

		if (TLC4BGlobals.isRunTLC()) {
			MP.TLCOutputStream.changeOutputStream();
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension,
					tlc4b.buildDir);
			MP.TLCOutputStream.resetOutputStream();
			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			tlc4b.printResults(results, false);
			System.exit(0);
		}
	}

	private void handleParameter(String[] args) {
		int index = 0;
		while (index < args.length) {
			if (args[index].toLowerCase().equals("-nodead")) {
				TLC4BGlobals.setDeadlockCheck(false);
			} else if (args[index].toLowerCase().equals("-notlc")) {
				TLC4BGlobals.setRunTLC(false);
			} else if (args[index].toLowerCase().equals("-notranslation")) {
				TLC4BGlobals.setTranslate(false);
			} else if (args[index].toLowerCase().equals("-nogoal")) {
				TLC4BGlobals.setGOAL(false);
			} else if (args[index].toLowerCase().equals("-noinv")) {
				TLC4BGlobals.setInvariant(false);
			} else if (args[index].toLowerCase().equals("-noass")) {
				TLC4BGlobals.setAssertionCheck(false);
			} else if (args[index].toLowerCase().equals("-wdcheck")) {
				TLC4BGlobals.setWelldefinednessCheck(true);
			} else if (args[index].toLowerCase().equals("-symmetry")) {
				TLC4BGlobals.setSymmetryUse(true);
			} else if (args[index].toLowerCase().equals("-tool")) {
				TLC4BGlobals.setTool(false);
			} else if (args[index].toLowerCase().equals("-tmp")) {
				buildDir = new File(System.getProperty("java.io.tmpdir"));
			} else if (args[index].toLowerCase().equals("-noltl")) {
				TLC4BGlobals.setCheckltl(false);
			} else if (args[index].toLowerCase().equals("-lazyconstants")) {
				TLC4BGlobals.setForceTLCToEvalConstants(false);
			} else if (args[index].toLowerCase().equals("-testscript")) {
				TLC4BGlobals.setRunTestscript(true);
			} else if (args[index].toLowerCase().equals("-notrace")) {
				TLC4BGlobals.setCreateTraceFile(false);
			} else if (args[index].toLowerCase().equals("-del")) {
				TLC4BGlobals.setDeleteOnExit(true);
			} else if (args[index].toLowerCase().equals("-parinveval")) {
				TLC4BGlobals.setPartialInvariantEvaluation(true);
			} else if (args[index].toLowerCase().equals("-log")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: File requiered after option '-log'.");
				}
				logFileString = args[index];

			} else if (args[index].toLowerCase().equals("-maxint")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: Number requiered after option '-maxint'.");
				}
				int maxint = Integer.parseInt(args[index]);
				TLC4BGlobals.setMAX_INT(maxint);
			} else if (args[index].toLowerCase().equals("-default_setsize")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: Number requiered after option '-default_setsize'.");
				}
				int deferredSetSize = Integer.parseInt(args[index]);
				TLC4BGlobals.setDEFERRED_SET_SIZE(deferredSetSize);
			} 
			else if (args[index].toLowerCase().equals("-minint")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: Number requiered after option '-minint'.");
				}
				int minint = Integer.parseInt(args[index]);
				TLC4BGlobals.setMIN_INT(minint);
				;
			} else if (args[index].toLowerCase().equals("-workers")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: Number requiered after option '-workers'.");
				}
				int workers = Integer.parseInt(args[index]);
				TLC4BGlobals.setWorkers(workers);
			} else if (args[index].toLowerCase().equals("-constantssetup")) {
				TLC4BGlobals.setProBconstantsSetup(true);
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: String requiered after option '-constantssetup'.");
				}
				constantsSetup = args[index];
			} else if (args[index].toLowerCase().equals("-ltlformula")) {
				index = index + 1;
				if (index == args.length) {
					throw new TLC4BIOException(
							"Error: LTL formula requiered after option '-ltlformula'.");
				}
				ltlFormula = args[index];
			} else if (args[index].charAt(0) == '-') {
				throw new TLC4BIOException("Error: unrecognized option: "
						+ args[index]);
			} else {
				if (filename != null) {
					throw new TLC4BIOException(
							"Error: more than one input files: " + filename
									+ " and " + args[index]);
				}
				filename = args[index];

			}
			index++;
		}
		if (filename == null) {
			throw new TLC4BIOException("Main machine required!");
		}
	}

	public void process(String[] args) throws IOException, BCompoundException {

		MP.print("Arguments: ");
		for (int i = 0; i < args.length; i++) {
			String string = args[i];
			MP.print(string);
			MP.print(" ");
		}
		println("");

		handleParameter(args);

		handleMainFileName();
		if (TLC4BGlobals.isTranslate()) {
			StopWatch.start(PARSING_TIME);
			MP.print("Parsing... ");
			translator = new Translator(machineFileNameWithoutFileExtension,
					mainfile, this.ltlFormula, this.constantsSetup);
			StopWatch.stop(PARSING_TIME);
			println("(" + StopWatch.getRunTimeAsString(PARSING_TIME) + "ms)");

			StopWatch.start(TRANSLATION_TIME);
			MP.print("Translating... ");
			translator.translate();
			this.tlaModule = translator.getModuleString();
			this.config = translator.getConfigString();
			this.tlcOutputInfo = translator.getTLCOutputInfo();
			StopWatch.stop(TRANSLATION_TIME);
			println("(" + StopWatch.getRunTimeAsString(TRANSLATION_TIME)
					+ "ms)");
			createFiles();
		}

	}

	private void handleMainFileName() {
		// the following lines fix incorrect file names
		filename = filename.replace("\\", File.separator);
		filename = filename.replace("/", File.separator);
		if (!filename.toLowerCase().endsWith(".mch")) {
			filename = filename + ".mch";
		}

		mainfile = new File(filename);
		if (!mainfile.exists()) {
			throw new TLC4BIOException("The file " + mainfile.getPath()
					+ " does not exist.");
		}
		try {
			mainfile = mainfile.getCanonicalFile();
		} catch (IOException e) {
			throw new TLC4BIOException("The file '" + mainfile.getPath()
					+ "' can not be accessed.");
		}

		machineFileNameWithoutFileExtension = mainfile.getName().substring(0,
				mainfile.getName().length() - 4); // deleting .mch

		if (buildDir == null) {
			buildDir = new File(mainfile.getParentFile(),
					machineFileNameWithoutFileExtension);
		}
	}

	private void createLogFile(Log log) {
		if (logFileString != null) {
			File logFile = new File(logFileString);
			FileWriter fw;
			boolean fileExists = logFile.exists();
			try {
				fw = new FileWriter(logFile, true); // the true will append the
													// new data
				if (!fileExists) {
					fw.write(log.getCSVFieldNamesLine());
				}
				fw.write(log.getCSVValueLine());
				fw.close();
				println("Log file: " + logFile.getAbsolutePath());
			} catch (IOException e) {
				new TLC4BIOException(e.getLocalizedMessage());
			}
		}
	}

	private void createFiles() {
		boolean dirCreated = buildDir.mkdir();
		if (dirCreated && TLC4BGlobals.isDeleteOnExit()) {
			buildDir.deleteOnExit();
		}

		File moduleFile = createFile(buildDir,
				machineFileNameWithoutFileExtension + ".tla", tlaModule,
				TLC4BGlobals.isDeleteOnExit());
		if (moduleFile != null) {
			println("TLA+ module '" + moduleFile.getAbsolutePath()
					+ "' created.");
		}

		File configFile = createFile(buildDir,
				machineFileNameWithoutFileExtension + ".cfg", config,
				TLC4BGlobals.isDeleteOnExit());
		if (configFile != null) {
			println("Configuration file '" + configFile.getAbsolutePath()
					+ "' created.");
		}

		createStandardModules();
	}

	private void createStandardModules() {
		for (STANDARD_MODULES module : translator
				.getStandardModuleToBeCreated()) {
			createStandardModule(buildDir, module.toString());
		}
	}

	private void createStandardModule(File path, String name) {
		// standard modules are copied from the standardModules folder to the
		// current directory

		File file = new File(path, name + ".tla");
		InputStream is = null;
		FileOutputStream fos = null;
		try {

			try {
				is = new FileInputStream("src/main/resources/standardModules/"
						+ name + ".tla");
			} catch (FileNotFoundException e) {
				is = this
						.getClass()
						.getClassLoader()
						.getResourceAsStream("standardModules/" + name + ".tla");
			}

			if (is == null) {
				// should never happen
				throw new TranslationException(
						"Unable to determine the source of the standard module: "
								+ name);
			}

			fos = new FileOutputStream(file);

			int read = 0;
			byte[] bytes = new byte[1024];

			while ((read = is.read(bytes)) != -1) {
				fos.write(bytes, 0, read);
			}
			println("Standard module '" + file.getName() + "' created.");
		} catch (IOException e) {
			throw new TLC4BIOException(e.getMessage());
		} finally {
			if (TLC4BGlobals.isDeleteOnExit() && file.exists()) {
				file.deleteOnExit();
			}
			try {
				if (is != null) {
					is.close();
				}
				if (fos != null) {
					fos.flush();
					fos.close();
				}
			} catch (IOException ex) {
				throw new TLC4BIOException(ex.getMessage());
			}
		}
	}

	public static File createFile(File dir, String fileName, String text,
			boolean deleteOnExit) {

		File file = new File(dir, fileName);
		boolean exists = false;
		try {
			exists = file.createNewFile();
			BufferedWriter out = new BufferedWriter(new OutputStreamWriter(
					new FileOutputStream(file), "UTF-8"));
			out.write(text);
			out.close();
			return file;
		} catch (UnsupportedEncodingException e1) {
			throw new TLC4BIOException(e1.getMessage());
		} catch (FileNotFoundException e1) {
			throw new TLC4BIOException(e1.getMessage());
		} catch (IOException e) {
			throw new TLC4BIOException(e.getMessage());
		} finally {
			if (deleteOnExit && exists) {
				file.deleteOnExit();
			}
		}
	}

	public File getBuildDir() {
		return buildDir;
	}

	public String getMachineFileNameWithoutFileExtension() {
		return machineFileNameWithoutFileExtension;
	}

	public File getMainFile(){
		return this.mainfile;
	}
	
}
