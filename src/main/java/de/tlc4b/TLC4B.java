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
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.*;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.exceptions.TLC4BException;
import de.tlc4b.exceptions.TranslationException;
import de.tlc4b.tlc.TLCOutputInfo;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;
import org.apache.commons.cli.*;

import static de.tlc4b.TLC4BCliOptions.*;
import static de.tlc4b.TLC4BCliOptions.TLCOption.*;
import static de.tlc4b.util.StopWatch.Watches.*;
import static de.tlc4b.MP.*;

public class TLC4B {

	private String filename;
	private File mainfile, traceFile;
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
		try {
			run(args);
		} catch (BCompoundException e) {
			printlnErr("***** Parsing Error *****");
			printlnErr(e.getMessage());
			System.exit(-1);
		} catch (TLC4BException e) {
			printlnErr(e.getMessage());
			println("Result: " + e.getError());
			System.exit(-1);
		} catch (IOException e) {
			printlnErr(e.getMessage());
			println("Result: " + "I/O Error");
			System.exit(-1);
		}
		System.exit(0);
	}

	/**
	 * API method to call TLC4B directly in Java
	 * @param args same arguments as for the CLI version
	 * @return results of TLC model check
	 */
	public static TLCResults run(String[] args) throws TLC4BException, IOException, BCompoundException {
		System.setProperty("apple.awt.UIElement", "true");
		// avoiding pop up window

		TLC4B tlc4b = new TLC4B();
		tlc4b.process(args);

		TLCResults results = null;
		if (TLC4BGlobals.isRunTLC()) {
			try {
				TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
				results = new TLCResults(tlc4b.tlcOutputInfo);
				results.evalResults();
				tlc4b.printResults(results);
				Log log = new Log(tlc4b, results);
				tlc4b.createLogFile(log);
			} catch (NoClassDefFoundError e) {
				printlnErr("Can not find TLC. The tlatools.jar must be included in the classpath.");
			}
		}
		return results;
	}

	/**
	 * Quickly check whether TLC4B is applicable to the provided machine.
	 *
	 * @param path path to B machine file
	 * @param timeOut time out in seconds
	 * @return Exception if TLC4B is not applicable, else null (also if unknown)
	 */
	public static Exception checkTLC4BIsApplicable(final String path, int timeOut) {
		Future<Exception> future = Executors.newSingleThreadExecutor().submit(() -> {
			try {
				TLC4B tlc4B = new TLC4B();
				tlc4B.processArgs(new String[]{path, SILENT.cliArg()});
				tlc4B.translate(false);
				return null;
			} catch (BCompoundException | IOException | TLC4BException e) {
				return e;
			}
		});

		try {
			return future.get(timeOut, TimeUnit.SECONDS);
		} catch (TimeoutException | InterruptedException | ExecutionException e) {
			future.cancel(true);
			return null; // unknown if TLC4B is applicable, exceptions can be ignored
		}
	}

	private void printResults(TLCResults results) {
		printOperationsCount(results);
		// options
		printlnSilent("Used Options");
		printlnSilent("| Number of workers: " + TLC4BGlobals.getWorkers());
		printlnSilent("| Invariants check: " + TLC4BGlobals.isInvariant());
		printlnSilent("| Deadlock check: " + TLC4BGlobals.isDeadlockCheck());
		printlnSilent("| Assertion check: " + TLC4BGlobals.isAssertion());
		printlnSilent("| Find Goal check: " + TLC4BGlobals.isGOAL());
		printlnSilent("| LTL formulas check: " + TLC4BGlobals.isCheckLTL());
		printlnSilent("| Partial invariant evaluation: " + TLC4BGlobals.isPartialInvariantEvaluation());
		printlnSilent("| Lazy constants setup: " + !TLC4BGlobals.isForceTLCToEvalConstants());
		printlnSilent("| Aggressive well-definedness check: " + TLC4BGlobals.checkWelldefinedness());
		printlnSilent("| ProB constant setup: " + TLC4BGlobals.isProBconstantsSetup());
		printlnSilent("| Symmetry reduction: " + TLC4BGlobals.useSymmetry());
		printlnSilent("| MIN Int: " + TLC4BGlobals.getMIN_INT());
		printlnSilent("| MAX Int: " + TLC4BGlobals.getMAX_INT());
		printlnSilent("| Standard deferred set size: " + TLC4BGlobals.getDEFERRED_SET_SIZE());
		printlnSilent("--------------------------------");
		if (TLC4BGlobals.isTranslate()) {
			printlnSilent("Parsing time: " + StopWatch.getRunTime(PARSING_TIME) + " ms");
			printlnSilent("Translation time: " + StopWatch.getRunTime(TRANSLATION_TIME) + " ms");
		}
		if (TLC4BGlobals.isRunTLC()) {
			println("Model checking time: " + results.getModelCheckingTime() + " sec");
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

			System.out.println(TLC4BGlobals.isCreateTraceFile());
			if (results.hasTrace() && TLC4BGlobals.isCreateTraceFile()) {
				String trace = results.getTrace();
				String tracefileName = machineFileNameWithoutFileExtension + ".tla.trace";
				traceFile = createFile(buildDir, tracefileName, trace, TLC4BGlobals.isDeleteOnExit());
				results.addTraceFilePath(traceFile.getAbsolutePath());
				println("Trace file '" + traceFile.getAbsolutePath() + "' created.");
			}
		}

	}

	public File getTraceFile() {
		return traceFile;
	}

	private void printOperationsCount(TLCResults results) {
		Map<String, Long> operationCount = results.getOperationCount();
		if (TLC4BGlobals.isPrintCoverage() && operationCount != null) {
			printlnSilent("---------- Coverage statistics ----------");
			for (Entry<String, Long> entry : operationCount.entrySet()) {
				printlnSilent(entry.getKey() + ": " + entry.getValue().toString());
			}
			printlnSilent("---------- End of coverage statistics ----------");
		}
	}

	public static void test(String[] args, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
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
			tlc4b.printResults(results);
			Log log = new Log(tlc4b, results);
			tlc4b.createLogFile(log);

			System.exit(0);
		}
	}

	public static void testString(String machineString, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4BGlobals.setTestingMode(true);
		// B2TLAGlobals.setCleanup(true);
		TLC4B tlc4b = new TLC4B();
		tlc4b.buildDir = new File("temp/");

		tlc4b.machineFileNameWithoutFileExtension = "Test";

		StopWatch.start(PARSING_TIME);
		printSilent("Parsing... ");
		tlc4b.translator = new Translator(machineString);
		StopWatch.stop(PARSING_TIME);
		printlnSilent("(" + StopWatch.getRunTimeAsString(PARSING_TIME) + "ms)");

		StopWatch.start(TRANSLATION_TIME);
		printSilent("Translating... ");
		tlc4b.translator.translate();
		tlc4b.tlaModule = tlc4b.translator.getModuleString();
		tlc4b.config = tlc4b.translator.getConfigString();
		tlc4b.tlcOutputInfo = tlc4b.translator.getTLCOutputInfo();
		StopWatch.stop(TRANSLATION_TIME);
		printlnSilent("(" + StopWatch.getRunTimeAsString(TRANSLATION_TIME) + "ms)");
		tlc4b.createFiles();

		if (TLC4BGlobals.isRunTLC()) {
			MP.TLCOutputStream.changeOutputStream();
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
			MP.TLCOutputStream.resetOutputStream();
			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			tlc4b.printResults(results);
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

			TLC4BGlobals.setVerbose(line.hasOption(VERBOSE.arg()));
			TLC4BGlobals.setSilent(line.hasOption(SILENT.arg()));
			TLC4BGlobals.setDeadlockCheck(!line.hasOption(NODEAD.arg()));
			TLC4BGlobals.setRunTLC(!line.hasOption(NOTLC.arg()));
			TLC4BGlobals.setTranslate(!line.hasOption(NOTRANSLATION.arg()));
			TLC4BGlobals.setGOAL(!line.hasOption(NOGOAL.arg()));
			TLC4BGlobals.setInvariant(!line.hasOption(NOINV.arg()));
			TLC4BGlobals.setAssertionCheck(!line.hasOption(NOASS.arg()));
			TLC4BGlobals.setWelldefinednessCheck(line.hasOption(WDCHECK.arg()));
			TLC4BGlobals.setSymmetryUse(line.hasOption(SYMMETRY.arg()));
			TLC4BGlobals.setTool(!line.hasOption(TOOL.arg()));
			TLC4BGlobals.setCheckltl(!line.hasOption(NOLTL.arg()));
			TLC4BGlobals.setForceTLCToEvalConstants(!line.hasOption(LAZYCONSTANTS.arg()));
			TLC4BGlobals.setRunTestscript(line.hasOption(TESTSCRIPT.arg()));
			TLC4BGlobals.setCreateTraceFile(!line.hasOption(NOTRACE.arg()));
			TLC4BGlobals.setDeleteOnExit(line.hasOption(DEL.arg()));
			TLC4BGlobals.setPartialInvariantEvaluation(line.hasOption(PARINVEVAL.arg()));
			TLC4BGlobals.setPrintCoverage(line.hasOption(COVERAGE.arg()));

			if (line.hasOption(TMP.arg())) {
				buildDir = new File(System.getProperty("java.io.tmpdir"));
			}
			if (line.hasOption(LOG.arg())) {
				logFileString = line.getOptionValue(LOG.arg());
				if (logFileString == null) {
					throw new TLC4BIOException("Error: File required after option '-log'.");
				}
			}
			if (line.hasOption(MAXINT.arg())) {
				String maxint = line.getOptionValue(MAXINT.arg());
				if (maxint == null) {
					throw new TLC4BIOException("Error: Number required after option '-maxint'.");
				}
				TLC4BGlobals.setMAX_INT(Integer.parseInt(maxint));
			}
			if (line.hasOption(DEFAULT_SETSIZE.arg())) {
				String deferredSetSize = line.getOptionValue(DEFAULT_SETSIZE.arg());
				if (deferredSetSize == null) {
					throw new TLC4BIOException("Error: Number required after option '-default_setsize'.");
				}
				TLC4BGlobals.setDEFERRED_SET_SIZE(Integer.parseInt(deferredSetSize));
			} 
			if (line.hasOption(MININT.arg())) {
				String minint = line.getOptionValue(MININT.arg());
				if (minint == null) {
					throw new TLC4BIOException("Error: Number required after option '-minint'.");
				}
				TLC4BGlobals.setMIN_INT(Integer.parseInt(minint));
			}
			if (line.hasOption(WORKERS.arg())) {
				String workers = line.getOptionValue(WORKERS.arg());
				if (workers == null) {
					throw new TLC4BIOException("Error: Number required after option '-workers'.");
				}
				TLC4BGlobals.setWorkers(Integer.parseInt(workers));
			}
			if (line.hasOption(DFID.arg())) {
				String dfid_initial_depth = line.getOptionValue(DFID.arg());
				if (dfid_initial_depth == null) {
					throw new TLC4BIOException("Error: Number required after option '-dfid'.");
				}
				TLC4BGlobals.setDfidInitialDepth(Integer.parseInt(dfid_initial_depth));
			}
			if (line.hasOption(CONSTANTSSETUP.arg())) {
				TLC4BGlobals.setProBconstantsSetup(true);
				constantsSetup = line.getOptionValue(CONSTANTSSETUP.arg());
				if (constantsSetup == null) {
					throw new TLC4BIOException("Error: String required after option '-constantssetup'.");
				}
			}
			if (line.hasOption(LTLFORMULA.arg())) {
				ltlFormula = line.getOptionValue(LTLFORMULA.arg());
				if (ltlFormula == null) {
					throw new TLC4BIOException("Error: LTL formula required after option '-ltlformula'.");
				}
			}
			if (line.hasOption(OUTPUT.arg())) {
				buildDir = new File(line.getOptionValue(OUTPUT.arg()));
			}
		} catch (ParseException e) {
			HelpFormatter formatter = new HelpFormatter();
			formatter.printHelp("[file]", options);
			throw new TLC4BIOException(e.getMessage());
		}
	}

	private void processArgs(String[] args) {
		handleParameter(args);
		handleMainFileName();

		MP.printVerbose("Arguments: ");
		for (String string : args) {
			MP.printVerbose(string);
			MP.printVerbose(" ");
		}
		printlnVerbose("");
	}

	private void translate(boolean createFiles) throws IOException, BCompoundException {
		StopWatch.start(PARSING_TIME);
		MP.printSilent("Parsing... ");
		translator = new Translator(machineFileNameWithoutFileExtension,
			mainfile, this.ltlFormula, this.constantsSetup);
		StopWatch.stop(PARSING_TIME);
		printlnSilent("(" + StopWatch.getRunTimeAsString(PARSING_TIME) + "ms)");

		StopWatch.start(TRANSLATION_TIME);
		MP.printSilent("Translating... ");
		translator.translate();
		this.tlaModule = translator.getModuleString();
		this.config = translator.getConfigString();
		this.tlcOutputInfo = translator.getTLCOutputInfo();
		StopWatch.stop(TRANSLATION_TIME);
		printlnSilent("(" + StopWatch.getRunTimeAsString(TRANSLATION_TIME) + "ms)");
		if (createFiles)
			createFiles();
	}

	public void process(String[] args) throws IOException, BCompoundException {
		processArgs(args);
		if (TLC4BGlobals.isTranslate()) {
			translate(true);
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
			try (FileWriter fw = new FileWriter(logFile, true)) { // the true will append the new data
				fw.write(log.getCSVString());
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

	public String getMachineFileNameWithoutFileExtension() {
		return machineFileNameWithoutFileExtension;
	}

	public File getMainFile(){
		return this.mainfile;
	}
	
}
