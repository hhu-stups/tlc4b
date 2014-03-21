package de.tlc4b;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;

import de.be4.classicalb.core.parser.exceptions.BException;
import de.tlc4b.TLC4BGlobals;
import de.tlc4b.analysis.UsedStandardModules.STANDARD_MODULES;
import de.tlc4b.exceptions.TLC4BIOException;
import de.tlc4b.exceptions.TLC4BException;
import de.tlc4b.tlc.TLCOutputInfo;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;

public class TLC4B {

	private String mainFileName;
	private String machineFileNameWithoutFileExtension;
	private String path;
	private String tlaModule;
	private String config;
	private Translator translator;
	private TLCOutputInfo tlcOutputInfo;
	private String ltlFormula;
	private String constantsSetup;

	public static void main(String[] args) throws IOException {
		System.setProperty("apple.awt.UIElement", "true"); // avoiding pop up
															// windows
		TLC4B tlc4b = new TLC4B();
		try {
			tlc4b.progress(args);
		} catch (BException e) {
			System.err.println("***** Parsing Error *****");
			System.err.println(e.getMessage());
			return;
		} catch (TLC4BException e) {
			System.err.println(e.getMessage());
			System.out.println("Model checking time: 0 sec");
			System.out.println("Result: " + e.getError());
			return;
		}

		if (TLC4BGlobals.isRunTLC()) {
			try {
				TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension,
						tlc4b.path);

				TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
				results.evalResults();
				tlc4b.printResults(results, TLC4BGlobals.isCreateTraceFile());
				System.exit(0);

			} catch (NoClassDefFoundError e) {
				System.err
						.println("Can not find TLC. The tlatools.jar must be included in the classpath.");
			}

		}

	}

	private void printResults(TLCResults results, boolean createTraceFile) {

		System.out.println("Parsing time: " + StopWatch.getRunTime("Parsing")
				+ " ms");
		System.out.println("Translation time: " + StopWatch.getRunTime("Pure")
				+ " ms");
		System.out.println("Model checking time: "
				+ results.getModelCheckingTime() + " sec");
		System.out.println("States analysed: "
				+ results.getNumberOfDistinctStates());
		System.out.println("Transitions fired: "
				+ results.getNumberOfTransitions());
		System.out.println("Result: " + results.getResultString());

		if (results.hasTrace() && createTraceFile) {
			String trace = results.getTrace();
			String tracefileName = machineFileNameWithoutFileExtension
					+ ".tla.trace";
			File traceFile = createFile(path, tracefileName, trace, false);
			if (traceFile != null) {
				System.out.println("Trace file '" + traceFile.getAbsolutePath()
						+ "' created.");
			}
		}

	}

	public static void test(String[] args, boolean deleteFiles)
			throws Exception {
		TLC4BGlobals.resetGlobals();
		TLC4BGlobals.setDeleteOnExit(deleteFiles);
		TLC4BGlobals.setCreateTraceFile(false);
		TLC4BGlobals.setTestingMode(true);
		// B2TLAGlobals.setCleanup(true);
		TLC4B tlc4b = new TLC4B();
		try {
			tlc4b.progress(args);
		} catch (Exception e) {
			e.printStackTrace();
			System.err.println(e.getMessage());
			throw e;
		}
		//System.out.println(tlc4b.tlaModule);
		if (TLC4BGlobals.isRunTLC()) {
			TLCRunner.runTLC(tlc4b.machineFileNameWithoutFileExtension,
					tlc4b.path);

			TLCResults results = new TLCResults(tlc4b.tlcOutputInfo);
			results.evalResults();
			// System.out.println("Result: " + results.getTLCResult());

			tlc4b.printResults(results, false);
			//System.out.println(results.getTrace());

			System.exit(0);
		}
	}

	/*
	 * private void printTestResultsForTestscript() { TLCResults tlcResults =
	 * null; // This output is adapted to Ivo's testscript
	 * System.out.println("------------- Results -------------");
	 * System.out.println("Model Checking Time: " +
	 * (tlcResults.getModelCheckingTime() * 1000) + " ms");
	 * System.out.println("States analysed: " +
	 * tlcResults.getNumberOfDistinctStates());
	 * System.out.println("Transitions fired: " +
	 * tlcResults.getNumberOfTransitions()); if (tlcResults.getTLCResult() !=
	 * TLCResult.NoError) { System.err.println("@@"); System.err.println("12" +
	 * tlcResults.getResultString()); }
	 * 
	 * }
	 */

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
			} else if (args[index].toLowerCase().equals("-wdcheck")) {
				TLC4BGlobals.setWelldefinednessCheck(true);
			} else if (args[index].toLowerCase().equals("-tool")) {
				TLC4BGlobals.setTool(false);
			} else if (args[index].toLowerCase().equals("-tmp")) {
				path = System.getProperty("java.io.tmpdir");
			} else if (args[index].toLowerCase().equals("-noltl")) {
				TLC4BGlobals.setCheckltl(false);
			} else if (args[index].toLowerCase().equals("-lazyconstants")) {
				TLC4BGlobals.setForceTLCToEvalConstants(false);
			} else if (args[index].toLowerCase().equals("-testscript")) {
				TLC4BGlobals.setRunTestscript(true);
			} else if (args[index].toLowerCase().equals("-notrace")) {

			} else if (args[index].toLowerCase().equals("-del")) {
				TLC4BGlobals.setDeleteOnExit(true);
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
				if (mainFileName != null) {
					throw new TLC4BIOException(
							"Error: more than one input files: " + mainFileName
									+ " and " + args[index]);
				}
				mainFileName = args[index];

			}
			index++;
		}
		if (mainFileName == null) {
			throw new TLC4BIOException("Main machine required!");
		}
	}

	private void progress(String[] args) throws IOException, BException {
		handleParameter(args);

		handleMainFileName();
		if (TLC4BGlobals.isTranslate()) {
			StopWatch.start("Parsing");
			translator = new Translator(machineFileNameWithoutFileExtension,
					getFile(), this.ltlFormula, this.constantsSetup);
			StopWatch.stop("Parsing");
			StopWatch.start("Pure");
			translator.translate();
			this.tlaModule = translator.getModuleString();
			this.config = translator.getConfigString();
			this.tlcOutputInfo = translator.getTLCOutputInfo();
			createFiles();
			StopWatch.stop("Pure");
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
		if (path == null) {
			if (name.contains(File.separator)) {
				path = name.substring(0, name.lastIndexOf(File.separator) + 1);
			} else {
				path = "." + File.separator;
			}
		}

		machineFileNameWithoutFileExtension = name.substring(name
				.lastIndexOf(File.separator) + 1);
	}

	private void createFiles() {
		File moduleFile = createFile(path, machineFileNameWithoutFileExtension
				+ ".tla", tlaModule, TLC4BGlobals.isDeleteOnExit());
		if (moduleFile != null) {
			System.out.println("TLA+ module '" + moduleFile.getAbsolutePath()
					+ "' created.");
		}

		File configFile = createFile(path, machineFileNameWithoutFileExtension
				+ ".cfg", config, TLC4BGlobals.isDeleteOnExit());
		if (configFile != null) {
			System.out.println("Configuration file '"
					+ configFile.getAbsolutePath() + "' created.");
		}
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
				STANDARD_MODULES.BBuiltIns)) {
			createStandardModule(path, STANDARD_MODULES.BBuiltIns.toString());
		}

		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.FunctionsAsRelations)) {
			createStandardModule(path,
					STANDARD_MODULES.FunctionsAsRelations.toString());
			if (!translator.getUsedStandardModule().contains(
					STANDARD_MODULES.Functions)) {
				createStandardModule(path,
						STANDARD_MODULES.Functions.toString());
			}
		}

		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.SequencesExtended)) {
			createStandardModule(path,
					STANDARD_MODULES.SequencesExtended.toString());
		}

		if (translator.getUsedStandardModule().contains(
				STANDARD_MODULES.SequencesAsRelations)) {
			createStandardModule(path,
					STANDARD_MODULES.SequencesAsRelations.toString());

			if (!translator.getUsedStandardModule().contains(
					STANDARD_MODULES.Relations)) {
				createStandardModule(path,
						STANDARD_MODULES.Relations.toString());
			}

			if (!translator.getUsedStandardModule().contains(
					STANDARD_MODULES.FunctionsAsRelations)) {
				createStandardModule(path,
						STANDARD_MODULES.FunctionsAsRelations.toString());
			}

			if (!translator.getUsedStandardModule().contains(
					STANDARD_MODULES.Functions)) {
				createStandardModule(path,
						STANDARD_MODULES.Functions.toString());
			}
		}
	}

	private void createStandardModule(String path, String name) {
		// standard modules are copied from the standardModules folder to the
		// current directory

		File file = new File(path + File.separator + name + ".tla");
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
			fos = new FileOutputStream(file);

			int read = 0;
			byte[] bytes = new byte[1024];

			while ((read = is.read(bytes)) != -1) {
				fos.write(bytes, 0, read);
			}
			System.out.println("Standard module '" + path + name
					+ ".tla' created.");
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

	private File getFile() {
		File mainFile = new File(mainFileName);
		if (!mainFile.exists()) {
			throw new TLC4BIOException("The file " + mainFileName
					+ " does not exist.");
		}
		return mainFile;
	}

	public static File createFile(String dir, String fileName, String text,
			boolean deleteOnExit) {
		File file = new File(dir + File.separator + fileName);

		BufferedWriter out;
		try {
			out = new BufferedWriter(new OutputStreamWriter(
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
		} finally{
			if (deleteOnExit && file.exists()) {
				file.deleteOnExit();
			}
		}
		
//		try {
//			out = new BufferedWriter(new OutputStreamWriter(
//					new FileOutputStream(file), "UTF-8"));
//			out.write(text);
//			out.close();
//			// FileWriter fw;
//			// fw = new FileWriter(file);
//			// fw.write(text);
//			// fw.close();
//			return file;
//		} catch (IOException e) {
//			e.printStackTrace();
//			throw new TLC4BIOException(e.getMessage());
//		} finally {
//			try {
//				out.close();
//			} catch (IOException e) {
//				e.printStackTrace();
//				throw new TLC4BIOException(e.getMessage());
//			}
//		}
	}

}
