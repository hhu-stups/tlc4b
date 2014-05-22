package de.tlc4b.tlc.integration;

import static org.junit.Assert.assertEquals;
import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.test;

import org.junit.Test;


public class SpecialTest {

	@Test
	public void testConstantSetup() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantsSetup", "(a = 1 &  b = 1) or (a = 1 &  b = 2)" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testConstantSetup2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantsSetup", "a = 1 &  b = 1" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testConstantSetup3() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantSetup.mch",
				"-constantsSetup", "(a = 1 &  b = 1) or (a = 2 &  b = 2)" };
		assertEquals(NoError, test(a));
	}
	
	
	@Test
	public void testConstantSetupFile2() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/ConstantsSetup2.mch",
				"-constantsSetup", "a = {(1,TRUE)}" };
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
	
	
}
