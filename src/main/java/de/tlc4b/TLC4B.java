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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.exceptions.TLC4BException;
import de.tlc4b.exceptions.TranslationException;
import de.tlc4b.tlc.TLCOutputInfo;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;
import org.apache.commons.cli.*;

import static de.tlc4b.util.StopWatch.Watches.*;
import static de.tlc4b.MP.*;

public class TLC4B {

	public static final String NODEAD = "nodead";
	public static final String NOTLC = "notlc";
	public static final String NOTRANSLATION = "notranslation";
	public static final String NOGOAL = "nogoal";
	public static final String NOINV = "noinv";
	public static final String NOASS = "noass";
	public static final String WDCHECK = "wdcheck";
	public static final String SYMMETRY = "symmetry";
	public static final String TOOL = "tool";
	public static final String TMP = "tmp";
	public static final String NOLTL = "noltl";
	public static final String LAZYCONSTANTS = "lazyconstants";
	public static final String TESTSCRIPT = "testscript";
	public static final String NOTRACE = "notrace";
	public static final String DEL = "del";
	public static final String PARINVEVAL = "parinveval";
	public static final String LOG = "log";
	public static final String MAXINT = "maxint";
	public static final String DEFAULT_SETSIZE = "default_setsize";
	public static final String MININT = "minint";
	public static final String WORKERS = "workers";
	public static final String CONSTANTSSETUP = "constantssetup";
	public static final String LTLFORMULA = "ltlformula";
	public static final String VERBOSE = "verbose";

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
				TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
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
		println("| Aggressive well-definedness check: "
				+ TLC4BGlobals.checkWelldefinedness());
		println("| ProB constant setup: " + TLC4BGlobals.isProBconstantsSetup());
		println("| Symmetry reduction: " + TLC4BGlobals.useSymmetry());
		println("| MIN Int: " + TLC4BGlobals.getMIN_INT());
		println("| MAX Int: " + TLC4BGlobals.getMAX_INT());
		println("| Standard deferred set size: "
				+ TLC4BGlobals.getDEFERRED_SET_SIZE());
		println("--------------------------------");
		println("Parsing time: " + StopWatch.getRunTime(PARSING_TIME) + " ms");
		println("Translation time: " + StopWatch.getRunTime(TRANSLATION_TIME)
				+ " ms");
		println("Model checking time: " + results.getModelCheckingTime()
				+ " sec");
		// MP.printMessage("Number of workers: " +
		// TLCGlobals.getNumWorkers());
		if (!results.getViolatedAssertions().isEmpty()) {
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
			String tracefileName = machineFileNameWithoutFileExtension + ".tla.trace";
			File traceFile = createFile(mainfile.getParentFile(), tracefileName, trace, false);
			println("Trace file '" + traceFile.getAbsolutePath() + "' created.");
		}

	}

	private void printOperationsCount(TLCResults results) {
		LinkedHashMap<String, Long> operationCount = results.getOperationCount();
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

	public static void test(String[] args, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
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
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
			MP.TLCOutputStream.resetOutputStream();
			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			tlc4b.printResults(results, false);

			System.exit(0);
		}
	}

	public static void testString(String machineString, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
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
		DefaultParser parser = new DefaultParser();
		Options options = getCommandlineOptions();
		try {
			CommandLine line = parser.parse(options, args);

			String[] remainingArgs = line.getArgs();
			if (remainingArgs.length != 1) {
				throw new TLC4BIOException("Main machine required!");
			} else {
				filename = remainingArgs[0];
			}

			TLC4BGlobals.setVerbose(line.hasOption(VERBOSE));
			TLC4BGlobals.setDeadlockCheck(!line.hasOption(NODEAD));
			TLC4BGlobals.setRunTLC(!line.hasOption(NOTLC));
			TLC4BGlobals.setTranslate(!line.hasOption(NOTRANSLATION));
			TLC4BGlobals.setGOAL(!line.hasOption(NOGOAL));
			TLC4BGlobals.setInvariant(!line.hasOption(NOINV));
			TLC4BGlobals.setAssertionCheck(!line.hasOption(NOASS));
			TLC4BGlobals.setWelldefinednessCheck(line.hasOption(WDCHECK));
			TLC4BGlobals.setSymmetryUse(line.hasOption(SYMMETRY));
			TLC4BGlobals.setTool(!line.hasOption(TOOL));
			TLC4BGlobals.setCheckltl(!line.hasOption(NOLTL));
			TLC4BGlobals.setForceTLCToEvalConstants(!line.hasOption(LAZYCONSTANTS));
			TLC4BGlobals.setRunTestscript(line.hasOption(TESTSCRIPT));
			TLC4BGlobals.setCreateTraceFile(!line.hasOption(NOTRACE));
			TLC4BGlobals.setDeleteOnExit(line.hasOption(DEL));
			TLC4BGlobals.setPartialInvariantEvaluation(line.hasOption(PARINVEVAL));

			if (line.hasOption(TMP)) {
				buildDir = new File(System.getProperty("java.io.tmpdir"));
			}
			if (line.hasOption(LOG)) {
				logFileString = line.getOptionValue(LOG);
				if (logFileString == null) {
					throw new TLC4BIOException("Error: File required after option '-log'.");
				}
			}
			if (line.hasOption(MAXINT)) {
				String maxint = line.getOptionValue(MAXINT);
				if (maxint == null) {
					throw new TLC4BIOException("Error: Number required after option '-maxint'.");
				}
				TLC4BGlobals.setMAX_INT(Integer.parseInt(maxint));
			}
			if (line.hasOption(DEFAULT_SETSIZE)) {
				String deferredSetSize = line.getOptionValue(DEFAULT_SETSIZE);
				if (deferredSetSize == null) {
					throw new TLC4BIOException("Error: Number required after option '-default_setsize'.");
				}
				TLC4BGlobals.setDEFERRED_SET_SIZE(Integer.parseInt(deferredSetSize));
			} 
			if (line.hasOption(MININT)) {
				String minint = line.getOptionValue(MININT);
				if (minint == null) {
					throw new TLC4BIOException("Error: Number required after option '-minint'.");
				}
				TLC4BGlobals.setMIN_INT(Integer.parseInt(minint));
			}
			if (line.hasOption(WORKERS)) {
				String workers = line.getOptionValue(WORKERS);
				if (workers == null) {
					throw new TLC4BIOException("Error: Number required after option '-workers'.");
				}
				TLC4BGlobals.setWorkers(Integer.parseInt(workers));
			}
			if (line.hasOption(CONSTANTSSETUP)) {
				TLC4BGlobals.setProBconstantsSetup(true);
				constantsSetup = line.getOptionValue(CONSTANTSSETUP);
				if (constantsSetup == null) {
					throw new TLC4BIOException("Error: String required after option '-constantssetup'.");
				}
			}
			if (line.hasOption(LTLFORMULA)) {
				ltlFormula = line.getOptionValue(LTLFORMULA);
				if (ltlFormula == null) {
					throw new TLC4BIOException("Error: LTL formula required after option '-ltlformula'.");
				}
			}
		} catch (ParseException e) {
			HelpFormatter formatter = new HelpFormatter();
			formatter.printHelp("[file]", options);
			throw new TLC4BIOException(e.getMessage());
		}
	}

	public void process(String[] args) throws IOException, BCompoundException {

		MP.printVerbose("Arguments: ");
		for (String string : args) {
			MP.printVerbose(string);
			MP.printVerbose(" ");
		}
		printlnVerbose("");

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
			println("(" + StopWatch.getRunTimeAsString(TRANSLATION_TIME) + "ms)");
			createFiles();
		}

	}

	private void handleMainFileName() {
		// the following lines fix incorrect file names
		filename = filename.replace("\\", File.separator);
		filename = filename.replace("/", File.separator);
		if (!filename.toLowerCase().endsWith(".mch") && !filename.toLowerCase().endsWith(".sys")) {
			filename = filename + ".mch";
		}

		mainfile = new File(filename);
		if (!mainfile.exists()) {
			throw new TLC4BIOException("The file " + mainfile.getPath() + " does not exist.");
		}
		try {
			mainfile = mainfile.getCanonicalFile();
		} catch (IOException e) {
			throw new TLC4BIOException("The file '" + mainfile.getPath() + "' can not be accessed.");
		}

		machineFileNameWithoutFileExtension = mainfile.getName().substring(0,
				mainfile.getName().length() - 4); // deleting .mch

		if (buildDir == null) {
			buildDir = new File(mainfile.getParentFile(), machineFileNameWithoutFileExtension);
		}
	}

	private void createLogFile(Log log) {
		if (logFileString != null) {
			File logFile = new File(logFileString);
			boolean exists = logFile.exists();
			try (FileWriter fw = new FileWriter(logFile, true)) { // the true will append the new data
				if (!exists) {
					fw.write(log.getCSVFieldNamesLine());
				}
				fw.write(log.getCSVValueLine());
				fw.close();
				println("Log file: " + logFile.getAbsolutePath());
			} catch (IOException e) {
				throw new TLC4BIOException(e.getLocalizedMessage());
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
		println("TLA+ module '" + moduleFile.getAbsolutePath() + "' created.");

		File configFile = createFile(buildDir,
				machineFileNameWithoutFileExtension + ".cfg", config,
				TLC4BGlobals.isDeleteOnExit());
		println("Configuration file '" + configFile.getAbsolutePath() + "' created.");

		createStandardModules();
	}

	private void createStandardModules() {
		for (STANDARD_MODULES module : translator.getStandardModuleToBeCreated()) {
			createStandardModule(buildDir, module.toString());
		}
	}

	private void createStandardModule(File path, String name) {
		// standard modules are copied from the standardModules folder to the current directory

		File file = new File(path, name + ".tla");
		InputStream is = null;
		FileOutputStream fos = null;
		try {

			try {
				is = new FileInputStream("src/main/resources/standardModules/" + name + ".tla");
			} catch (FileNotFoundException e) {
				is = this
						.getClass()
						.getClassLoader()
						.getResourceAsStream("standardModules/" + name + ".tla");
			}

			if (is == null) {
				// should never happen
				throw new TranslationException("Unable to determine the source of the standard module: " + name);
			}

			fos = new FileOutputStream(file);

			int read;
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

	public static File createFile(File dir, String fileName, String text, boolean deleteOnExit) {

		File file = new File(dir, fileName);
		boolean exists = false;
		try {
			exists = file.createNewFile();
			BufferedWriter out = new BufferedWriter(new OutputStreamWriter(
				Files.newOutputStream(file.toPath()), StandardCharsets.UTF_8));
			out.write(text);
			out.close();
			return file;
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

	private static Options getCommandlineOptions() {
		Options options = new Options();

		options.addOption(NODEAD, "do not look for deadlocks (for model check, animate, execute)");
		options.addOption(NOTLC, "");
		options.addOption(NOTRANSLATION, "");
		options.addOption(NOGOAL, "");
		options.addOption(NOINV, "");
		options.addOption(NOASS, "");
		options.addOption(WDCHECK, "");
		options.addOption(SYMMETRY, "");
		options.addOption(TOOL, "");
		options.addOption(TMP, "");
		options.addOption(NOLTL, "");
		options.addOption(LAZYCONSTANTS, "");
		options.addOption(TESTSCRIPT, "");
		options.addOption(NOTRACE, "");
		options.addOption(DEL, "");
		options.addOption(PARINVEVAL, "");
		options.addOption(LOG, true, "write statistics to CSV file");
		options.addOption(MAXINT, true, "");
		options.addOption(DEFAULT_SETSIZE, true, "");
		options.addOption(MININT, true, "");
		options.addOption(WORKERS, true, "");
		options.addOption(CONSTANTSSETUP, true, "use constants found by ProB for TLC model checking");
		options.addOption(LTLFORMULA, true, "");
		options.addOption(VERBOSE, "put TLC4B in verbose mode");

		return options;
	}
	
}
