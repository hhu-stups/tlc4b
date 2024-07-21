package de.tlc4b.tlc.integration;

import static de.tlc4b.TLC4BCliOptions.TLCOption.OUTPUT;
import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.test;
import static org.junit.Assert.*;

import org.junit.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;


public class SpecialTest {

	@Test
	public void testConstantSetup() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "(a = 1 &  b = 1) or (a = 1 &  b = 2)" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testConstantSetup2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "a = 1 &  b = 1" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testConstantSetup3() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantssetup", "(a = 1 &  b = 1) or (a = 2 &  b = 2)" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testConstantSetupFile2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantsSetup2.mch",
				"-constantssetup", "a = {(1,TRUE)}" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testTraceFile() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/TraceCheck.mch"};
		assertEquals(Deadlock, test(a));
	}
	
	@Test
	public void testDefinitionsLoad() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/LoadDefinitions.mch"};
		assertEquals(NoError, test(a));
	}

	@Test
	public void testCustomOutputDir() throws Exception {
		Path specialDir = Paths.get("./src/test/resources/special/veryspecialoutput");
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch", OUTPUT.cliArg(), specialDir.toString()};
		assertEquals(InvariantViolation, test(a));

		assertTrue(Files.deleteIfExists(specialDir.resolve("InvariantError.tla")));
		assertTrue(Files.deleteIfExists(specialDir.resolve("InvariantError.cfg")));
		assertTrue(Files.deleteIfExists(specialDir));
	}
	
}
