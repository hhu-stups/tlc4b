package de.tlc4b;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.tlc4b.exceptions.TLC4BException;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.exceptions.TranslationException;
import de.tlc4b.tlc.TLCOutputInfo;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.help.HelpFormatter;

public class TLC4B {
	private static final String CSV_DELIMITER = ";";

	private File mainfile;
	private File traceFile;
	private String machineFileNameWithoutFileExtension;
	// e.g. Test of file foo/bar/Test.mch
	private File logFile;

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
			MP.printlnErr("***** Parsing Error *****");
			MP.printlnErr(e.getMessage());
			System.exit(-1);
		} catch (TLC4BException e) {
			MP.printlnErr(e.getMessage());
			MP.println("Result: " + e.getError());
			System.exit(-1);
		} catch (IOException e) {
			MP.printlnErr(e.getMessage());
			MP.println("Result: " + "I/O Error");
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
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up window

		TLC4B tlc4b = new TLC4B();
		tlc4b.process(args);

		TLCResults results = null;
		if (TLC4BGlobals.isRunTLC()) {
			try {
				TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
				results = new TLCResults(tlc4b.tlcOutputInfo);
				results.evalResults();
				tlc4b.printResults(results);
				tlc4b.createLogFile(results);
			} catch (NoClassDefFoundError e) {
				MP.printlnErr("Can not find TLC. The tlatools.jar must be included in the classpath.");
			}
		}
		return results;
	}

	/**
	 * Check whether TLC4B (translation) is applicable to the provided machine.
	 * This method has no return value - if it returns without throwing an exception, then TLC4B is applicable.
	 * Be aware that this method may take a long time to run for large/complex machines.
	 *
	 * @param path path to B machine file
	 * @throws BCompoundException if the machine file could not be parsed
	 * @throws TLC4BException if translation fails for any other reason
	 */
	public static void checkTLC4BIsApplicable(String path) throws BCompoundException {
		checkTLC4BIsApplicable(path, false);
	}

	/**
	 * Check whether TLC4B is applicable to the provided machine.
	 * This method has no return value - if it returns without throwing an exception, then TLC4B is applicable.
	 * Be aware that this method may take a long time to run for large/complex machines.
	 *
	 * @param path path to B machine file
	 * @param noTranslation if a translation is not required
	 * @throws BCompoundException if the machine file could not be parsed
	 * @throws TLC4BException if translation fails for any other reason
	 */
	public static void checkTLC4BIsApplicable(String path, boolean noTranslation) throws BCompoundException {
		TLC4B tlc4B = new TLC4B();
		List<String> args = new ArrayList<>();
		args.add(path);
		args.add(TLC4BOption.SILENT.cliArg());
		if (noTranslation) {
			args.add(TLC4BOption.NOTRANSLATION.cliArg());
		}
		tlc4B.processArgs(args.toArray(new String[0]));
		if (TLC4BGlobals.isTranslate()) {
			tlc4B.translate();
			// tlc4B.createFiles() is intentionally not called here!
		}
		// TODO: verify if machine can be checked with TLC
	}

	private void printResults(TLCResults results) throws IOException {
		printOperationsCount(results);
		// options
		MP.printlnSilent("Used Options");
		if (TLC4BGlobals.getDfidInitialDepth() > 0) // -1 if disabled
			MP.printlnSilent("| Use DFS with initial depth: " + TLC4BGlobals.getDfidInitialDepth());
		MP.printlnSilent("| Number of workers: " + TLC4BGlobals.getWorkers());
		MP.printlnSilent("| Invariants check: " + TLC4BGlobals.isInvariant());
		MP.printlnSilent("| Deadlock check: " + TLC4BGlobals.isDeadlockCheck());
		MP.printlnSilent("| Assertion check: " + TLC4BGlobals.isAssertion());
		MP.printlnSilent("| Find Goal check: " + TLC4BGlobals.isGOAL());
		MP.printlnSilent("| LTL formulas check: " + TLC4BGlobals.isCheckLTL());
		MP.printlnSilent("| Partial invariant evaluation: " + TLC4BGlobals.isPartialInvariantEvaluation());
		MP.printlnSilent("| Lazy constants setup: " + !TLC4BGlobals.isForceTLCToEvalConstants());
		MP.printlnSilent("| Aggressive well-definedness check: " + TLC4BGlobals.checkWelldefinedness());
		MP.printlnSilent("| ProB constant setup: " + TLC4BGlobals.isProBconstantsSetup());
		MP.printlnSilent("| Symmetry reduction: " + TLC4BGlobals.useSymmetry());
		MP.printlnSilent("| MIN Int: " + TLC4BGlobals.getMIN_INT());
		MP.printlnSilent("| MAX Int: " + TLC4BGlobals.getMAX_INT());
		MP.printlnSilent("| Standard deferred set size: " + TLC4BGlobals.getDEFERRED_SET_SIZE());
		MP.printlnSilent("--------------------------------");
		if (TLC4BGlobals.isTranslate()) {
			MP.printlnSilent("Parsing time: " + StopWatch.getRunTime(StopWatch.Watches.PARSING_TIME) + " ms");
			MP.printlnSilent("Translation time: " + StopWatch.getRunTime(StopWatch.Watches.TRANSLATION_TIME) + " ms");
		}
		if (TLC4BGlobals.isRunTLC()) {
			MP.println("Model checking time: " + results.getModelCheckingTime() + " sec");
			// MP.printMessage("Number of workers: " +
			// TLCGlobals.getNumWorkers());
			if (!results.getViolatedAssertions().isEmpty()) {
				MP.println("Violated assertions: " + results.getViolatedAssertions());
			}
			MP.println("States analysed: " + results.getNumberOfDistinctStates());
			MP.println("Transitions fired: " + results.getNumberOfTransitions());
			MP.println("Result: " + results.getResultString());
			String violatedDefinition = results.getViolatedDefinition();
			if (violatedDefinition != null) {
				MP.println("Violated Definition: " + violatedDefinition);
			}

			if (results.hasTrace() && TLC4BGlobals.isCreateTraceFile()) {
				String trace = results.getTrace();
				if (trace != null) {
					String tracefileName = machineFileNameWithoutFileExtension + ".tla.trace";
					traceFile = createFile(buildDir, tracefileName, trace, TLC4BGlobals.isDeleteOnExit());
					results.addTraceFilePath(traceFile.getAbsolutePath());
					MP.println("Trace file '" + traceFile.getAbsolutePath() + "' created.");
				}
			}
		}

	}

	private void printOperationsCount(TLCResults results) {
		Map<String, Long> operationCount = results.getOperationCount();
		if (TLC4BGlobals.isPrintCoverage() && operationCount != null) {
			MP.printlnSilent("---------- Coverage statistics ----------");
			for (Map.Entry<String, Long> entry : operationCount.entrySet()) {
				MP.printlnSilent(entry.getKey() + ": " + entry.getValue().toString());
			}
			MP.printlnSilent("---------- End of coverage statistics ----------");
		}
	}

	public static void test(String[] args, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4B tlc4b = new TLC4B();
		try {
			tlc4b.process(args);
		} catch (Exception e) {
			e.printStackTrace();
			MP.printlnErr(e.getMessage());
			throw e;
		}
		if (TLC4BGlobals.isRunTLC()) {
			MP.TLCOutputStream.changeOutputStream();
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension, tlc4b.buildDir);
			MP.TLCOutputStream.resetOutputStream();
			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			tlc4b.printResults(results);
			tlc4b.createLogFile(results);

			System.exit(0);
		}
	}

	public static void testString(String machineString, boolean deleteFiles) throws Exception {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up windows
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4B tlc4b = new TLC4B();
		tlc4b.buildDir = new File("temp/");

		tlc4b.machineFileNameWithoutFileExtension = "Test";

		StopWatch.start(StopWatch.Watches.PARSING_TIME);
		MP.printSilent("Parsing... ");
		tlc4b.translator = new Translator(machineString);
		StopWatch.stop(StopWatch.Watches.PARSING_TIME);
		MP.printlnSilent("(" + StopWatch.getRunTimeAsString(StopWatch.Watches.PARSING_TIME) + "ms)");

		StopWatch.start(StopWatch.Watches.TRANSLATION_TIME);
		MP.printSilent("Translating... ");
		tlc4b.translator.translate();
		tlc4b.tlaModule = tlc4b.translator.getModuleString();
		tlc4b.config = tlc4b.translator.getConfigString();
		tlc4b.tlcOutputInfo = tlc4b.translator.getTLCOutputInfo();
		StopWatch.stop(StopWatch.Watches.TRANSLATION_TIME);
		MP.printlnSilent("(" + StopWatch.getRunTimeAsString(StopWatch.Watches.TRANSLATION_TIME) + "ms)");
		MP.printlnSilent("Translated TLA:\n" + tlc4b.tlaModule);
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
	
	private static Options getCommandlineOptions() {
		Options options = new Options();
		for (TLC4BOption option : TLC4BOption.values()) {
			options.addOption(option.arg(), option.expectsArg() != null, option.desc());
		}
		return options;
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
				mainfile = new File(remainingArgs[0]);
			}

			// reset all parameters to default, then apply current args
			TLC4BGlobals.resetGlobals();
			TLC4BGlobals.setVerbose(line.hasOption(TLC4BOption.VERBOSE.arg()));
			TLC4BGlobals.setSilent(line.hasOption(TLC4BOption.SILENT.arg()));
			TLC4BGlobals.setDeadlockCheck(!line.hasOption(TLC4BOption.NODEAD.arg()));
			TLC4BGlobals.setRunTLC(!line.hasOption(TLC4BOption.NOTLC.arg()));
			TLC4BGlobals.setTranslate(!line.hasOption(TLC4BOption.NOTRANSLATION.arg()));
			TLC4BGlobals.setGOAL(!line.hasOption(TLC4BOption.NOGOAL.arg()));
			TLC4BGlobals.setInvariant(!line.hasOption(TLC4BOption.NOINV.arg()));
			TLC4BGlobals.setAssertionCheck(!line.hasOption(TLC4BOption.NOASS.arg()));
			TLC4BGlobals.setWelldefinednessCheck(line.hasOption(TLC4BOption.WDCHECK.arg()));
			TLC4BGlobals.setSymmetryUse(line.hasOption(TLC4BOption.SYMMETRY.arg()));
			TLC4BGlobals.setCheckltl(!line.hasOption(TLC4BOption.NOLTL.arg()));
			TLC4BGlobals.setForceTLCToEvalConstants(!line.hasOption(TLC4BOption.LAZYCONSTANTS.arg()));
			TLC4BGlobals.setCreateTraceFile(!line.hasOption(TLC4BOption.NOTRACE.arg()));
			TLC4BGlobals.setDeleteOnExit(line.hasOption(TLC4BOption.DEL.arg()));
			TLC4BGlobals.setPartialInvariantEvaluation(line.hasOption(TLC4BOption.PARINVEVAL.arg()));
			TLC4BGlobals.setPrintCoverage(line.hasOption(TLC4BOption.COVERAGE.arg()));

			if (line.hasOption(TLC4BOption.TMP.arg())) {
				buildDir = new File(System.getProperty("java.io.tmpdir"));
			}
			if (line.hasOption(TLC4BOption.LOG.arg())) {
				String logFileString = line.getOptionValue(TLC4BOption.LOG.arg());
				if (logFileString == null) {
					throw new TLC4BIOException("Error: File required after option '-log'.");
				}
				logFile = new File(logFileString);
			}
			if (line.hasOption(TLC4BOption.MAXINT.arg())) {
				String maxint = line.getOptionValue(TLC4BOption.MAXINT.arg());
				if (maxint == null) {
					throw new TLC4BIOException("Error: Number required after option '-maxint'.");
				}
				TLC4BGlobals.setMAX_INT(Integer.parseInt(maxint));
			}
			if (line.hasOption(TLC4BOption.DEFAULT_SETSIZE.arg())) {
				String deferredSetSize = line.getOptionValue(TLC4BOption.DEFAULT_SETSIZE.arg());
				if (deferredSetSize == null) {
					throw new TLC4BIOException("Error: Number required after option '-default_setsize'.");
				}
				TLC4BGlobals.setDEFERRED_SET_SIZE(Integer.parseInt(deferredSetSize));
			} 
			if (line.hasOption(TLC4BOption.MININT.arg())) {
				String minint = line.getOptionValue(TLC4BOption.MININT.arg());
				if (minint == null) {
					throw new TLC4BIOException("Error: Number required after option '-minint'.");
				}
				TLC4BGlobals.setMIN_INT(Integer.parseInt(minint));
			}
			if (line.hasOption(TLC4BOption.WORKERS.arg())) {
				String workers = line.getOptionValue(TLC4BOption.WORKERS.arg());
				if (workers == null) {
					throw new TLC4BIOException("Error: Number required after option '-workers'.");
				}
				TLC4BGlobals.setWorkers(Integer.parseInt(workers));
			}
			if (line.hasOption(TLC4BOption.DFID.arg())) {
				String dfid_initial_depth = line.getOptionValue(TLC4BOption.DFID.arg());
				if (dfid_initial_depth == null) {
					throw new TLC4BIOException("Error: Number required after option '-dfid'.");
				}
				TLC4BGlobals.setDfidInitialDepth(Integer.parseInt(dfid_initial_depth));
			}
			if (line.hasOption(TLC4BOption.CONSTANTSSETUP.arg())) {
				TLC4BGlobals.setProBconstantsSetup(true);
				constantsSetup = line.getOptionValue(TLC4BOption.CONSTANTSSETUP.arg());
				if (constantsSetup == null) {
					throw new TLC4BIOException("Error: String required after option '-constantssetup'.");
				}
			}
			if (line.hasOption(TLC4BOption.LTLFORMULA.arg())) {
				ltlFormula = line.getOptionValue(TLC4BOption.LTLFORMULA.arg());
				if (ltlFormula == null) {
					throw new TLC4BIOException("Error: LTL formula required after option '-ltlformula'.");
				}
			}
			if (line.hasOption(TLC4BOption.OUTPUT.arg())) {
				buildDir = new File(line.getOptionValue(TLC4BOption.OUTPUT.arg()));
			}
		} catch (ParseException e) {
			HelpFormatter formatter = HelpFormatter.builder()
				.setShowSince(false)
				.get();
			TLC4BException tlcException = new TLC4BIOException(e);
			try {
				formatter.printHelp("java -jar TLC4B.jar [file]", "", options, "", false);
			} catch (IOException exc) {
				tlcException.addSuppressed(exc);
			}
			throw tlcException;
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
		MP.printlnVerbose("");
	}

	private void translate() throws BCompoundException {
		StopWatch.start(StopWatch.Watches.PARSING_TIME);
		MP.printSilent("Parsing... ");
		translator = new Translator(machineFileNameWithoutFileExtension,
			mainfile, this.ltlFormula, this.constantsSetup);
		StopWatch.stop(StopWatch.Watches.PARSING_TIME);
		MP.printlnSilent("(" + StopWatch.getRunTimeAsString(StopWatch.Watches.PARSING_TIME) + "ms)");

		StopWatch.start(StopWatch.Watches.TRANSLATION_TIME);
		MP.printSilent("Translating... ");
		translator.translate();
		this.tlaModule = translator.getModuleString();
		this.config = translator.getConfigString();
		this.tlcOutputInfo = translator.getTLCOutputInfo();
		StopWatch.stop(StopWatch.Watches.TRANSLATION_TIME);
		MP.printlnSilent("(" + StopWatch.getRunTimeAsString(StopWatch.Watches.TRANSLATION_TIME) + "ms)");
	}

	public void process(String[] args) throws IOException, BCompoundException {
		processArgs(args);
		if (TLC4BGlobals.isTranslate()) {
			translate();
			createFiles();
		}
	}

	private void handleMainFileName() {
		if (!mainfile.exists()) {
			throw new TLC4BIOException("The file " + mainfile.getPath() + " does not exist.");
		}
		try {
			mainfile = mainfile.getCanonicalFile();
		} catch (IOException e) {
			throw new TLC4BIOException("The file '" + mainfile.getPath() + "' can not be accessed.", e);
		}

		String fileName = mainfile.getName();
		int lastDot = fileName.lastIndexOf('.');
		if (lastDot > 0) {
			machineFileNameWithoutFileExtension = fileName.substring(0, lastDot);
		} else{
			machineFileNameWithoutFileExtension = fileName;
		}

		if (buildDir == null) {
			buildDir = new File(mainfile.getParentFile(), machineFileNameWithoutFileExtension);
		}

		if (!TLC4BGlobals.isTranslate()) {
			// override buildDir because no files will be generated
			buildDir = mainfile.getParentFile();
		}
	}

	private String getLogCsvString(TLCResults tlcResults) {
		List<String> fieldNames = new ArrayList<>();
		List<String> fieldValues = new ArrayList<>();

		fieldNames.add("Machine File");
		String machineFile = mainfile.getAbsolutePath();
		fieldValues.add(machineFile);

		fieldNames.add("TLC Model Checking Time (s)");
		double tlcModelCheckingTime = tlcResults.getModelCheckingTime();
		fieldValues.add(String.valueOf(tlcModelCheckingTime));

		fieldNames.add("Parsing Time Of B machine (ms)");
		long parseTime = StopWatch.getRunTime(StopWatch.Watches.PARSING_TIME);
		fieldValues.add(String.valueOf(parseTime));

		fieldNames.add("Translation Time (ms)");
		long translationTime = StopWatch.getRunTime(StopWatch.Watches.TRANSLATION_TIME);
		fieldValues.add(String.valueOf(translationTime));

		fieldNames.add("Model Checking Time (ms)");
		long modelCheckingTime = StopWatch.getRunTime(StopWatch.Watches.MODEL_CHECKING_TIME);
		fieldValues.add(String.valueOf(modelCheckingTime));
		
		fieldNames.add("TLC Result");
		fieldValues.add(tlcResults.getResultString());

		fieldNames.add("States analysed");
		fieldValues.add(Integer.toString(tlcResults.getNumberOfDistinctStates()));

		fieldNames.add("Transitions fired");
		fieldValues.add(Integer.toString(tlcResults.getNumberOfTransitions()));

		fieldNames.add("Violated Definition");
		String violatedDefinition = tlcResults.getViolatedDefinition();
		fieldValues.add(violatedDefinition != null ? violatedDefinition : "");

		fieldNames.add("Violated Assertions");
		List<String> violatedAssertions = tlcResults.getViolatedAssertions();
		fieldValues.add(!violatedAssertions.isEmpty() ? String.join(CSV_DELIMITER, violatedAssertions) : "");

		fieldNames.add("Operation Coverage");
		Map<String, Long> operationCount = tlcResults.getOperationCount();
		List<String> opCountString = new ArrayList<>();
		if (operationCount != null) {
			operationCount.forEach((operation, count) -> opCountString.add(operation + CSV_DELIMITER + count));
		}
		fieldValues.add(!opCountString.isEmpty() ? String.join(CSV_DELIMITER, opCountString) : "");

		fieldNames.add("Trace File");
		fieldValues.add(traceFile != null ? traceFile.getAbsolutePath() : "");

		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < fieldNames.size(); i++) {
			sb.append(fieldNames.get(i)).append(CSV_DELIMITER).append(fieldValues.get(i)).append("\n");
		}
		return sb.toString();
	}

	private void createLogFile(TLCResults results) throws IOException {
		if (logFile != null) {
			String logCsvString = getLogCsvString(results);
			try (FileWriter fw = new FileWriter(logFile, true)) { // the true will append the new data
				fw.write(logCsvString);
			}
			MP.println("Log file: " + logFile.getAbsolutePath());
		}
	}

	private void createFiles() throws IOException {
		boolean dirCreated = buildDir.mkdir();
		if (dirCreated && TLC4BGlobals.isDeleteOnExit()) {
			buildDir.deleteOnExit();
		}

		File moduleFile = createFile(buildDir,
				machineFileNameWithoutFileExtension + ".tla", tlaModule,
				TLC4BGlobals.isDeleteOnExit());
		MP.println("TLA+ module '" + moduleFile.getAbsolutePath() + "' created.");

		File configFile = createFile(buildDir,
				machineFileNameWithoutFileExtension + ".cfg", config,
				TLC4BGlobals.isDeleteOnExit());
		MP.println("Configuration file '" + configFile.getAbsolutePath() + "' created.");

		createStandardModules();
	}

	private void createStandardModules() throws IOException {
		for (String module : translator.getStandardModuleToBeCreated()) {
			createStandardModule(buildDir, module);
		}
	}

	private void createStandardModule(File path, String name) throws IOException {
		// standard modules are copied from the standardModules folder to the current directory

		File file = new File(path, name + ".tla");
		InputStream resourceStream = TLC4B.class.getResourceAsStream("standardModules/" + name + ".tla");
		if (resourceStream == null) {
			// should never happen
			throw new TranslationException("Unable to determine the source of the standard module: " + name);
		}

		try (InputStream is = resourceStream; OutputStream fos = new FileOutputStream(file)) {
			int read;
			byte[] bytes = new byte[1024];

			while ((read = is.read(bytes)) != -1) {
				fos.write(bytes, 0, read);
			}
			MP.println("Standard module '" + file.getName() + "' created.");
		} finally {
			if (TLC4BGlobals.isDeleteOnExit() && file.exists()) {
				file.deleteOnExit();
			}
		}
	}

	private static File createFile(File dir, String fileName, String text, boolean deleteOnExit) throws IOException {
		File file = new File(dir, fileName);
		boolean exists = false;
		try {
			exists = file.createNewFile();
			try (Writer out = new BufferedWriter(new OutputStreamWriter(Files.newOutputStream(file.toPath()), StandardCharsets.UTF_8))) {
				out.write(text);
			}
			return file;
		} finally {
			if (deleteOnExit && exists) {
				file.deleteOnExit();
			}
		}
	}
}
