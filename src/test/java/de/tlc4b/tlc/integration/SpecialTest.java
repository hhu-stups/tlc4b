package de.tlc4b.tlc.integration;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import de.tlc4b.TLC4BOption;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SpecialTest {

	@Test
	public void testConstantSetup() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "(a = 1 &  b = 1) or (a = 1 &  b = 2)" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testConstantSetup2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "a = 1 &  b = 1" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testConstantSetup3() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "(a = 1 &  b = 1) or (a = 2 &  b = 2)" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testConstantSetupFile2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantsSetup2.mch",
				"-constantssetup", "a = {(1,TRUE)}" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testTraceFile() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/TraceCheck.mch"};
		assertEquals(TLCResults.TLCResult.Deadlock, TestUtil.test(a));
	}
	
	@Test
	public void testDefinitionsLoad() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/LoadDefinitions.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}

	@Test
	public void testCustomOutputDir() throws Exception {
		Path specialDir = Paths.get("./src/test/resources/special/veryspecialoutput");
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch", TLC4BOption.OUTPUT.cliArg(), specialDir.toString()};
		assertEquals(TLCResults.TLCResult.InvariantViolation, TestUtil.testWithTrace(a));

		assertTrue(Files.deleteIfExists(specialDir.resolve("InvariantError.tla")));
		assertTrue(Files.deleteIfExists(specialDir.resolve("InvariantError.cfg")));
		assertTrue(Files.deleteIfExists(specialDir.resolve("InvariantError.tla.trace")));
		assertTrue(Files.deleteIfExists(specialDir));
	}

	@Test
	public void testLogFile() throws Exception {
		Path logFile = Paths.get("./src/test/resources/special/log.csv");
		Path machineFile = Paths.get("./src/test/resources/special/SimpleForLog.mch");
		Path tracePath = Paths.get("./src/test/resources/special/SimpleForLog/SimpleForLog.tla.trace");
		logFile.toFile().delete();

		String[] a = new String[] { machineFile.toString(), TLC4BOption.LOG.cliArg(), logFile.toString(), TLC4BOption.COVERAGE.cliArg()};
		assertEquals(TLCResults.TLCResult.InvariantViolation, TestUtil.testWithTrace(a));

		List<String> lines = Files.readAllLines(logFile);
		assertEquals(lines.size(), 12);
		assertEquals(lines.get(0), "Machine File;" + machineFile.toRealPath());
		assertTrue(lines.get(1).startsWith("TLC Model Checking Time (s);"));
		assertTrue(lines.get(2).startsWith("Parsing Time Of B machine (ms);"));
		assertTrue(lines.get(3).startsWith("Translation Time (ms);"));
		assertTrue(lines.get(4).startsWith("Model Checking Time (ms);"));
		assertEquals(lines.get(5), "TLC Result;Invariant Violation");
		assertEquals(lines.get(6), "States analysed;5");
		assertEquals(lines.get(7), "Transitions fired;5");
		assertEquals(lines.get(8), "Violated Definition;Invariant1");
		assertEquals(lines.get(9), "Violated Assertions;");
		assertEquals(lines.get(10), "Operation Coverage;inc;8");
		assertEquals(lines.get(11), "Trace File;" + tracePath.toRealPath());

		assertTrue(Files.deleteIfExists(tracePath));
		assertTrue(Files.deleteIfExists(logFile));
	}
	
}
