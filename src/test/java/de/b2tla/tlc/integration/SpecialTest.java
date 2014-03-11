package de.b2tla.tlc.integration;

import static de.b2tla.util.TestUtil.test;
import static org.junit.Assert.assertEquals;
import static de.b2tla.tlc.TLCResults.TLCResult.*;

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
	public void testTraceFile() throws Exception {
		String[] a = new String[] {
				"./src/test/resources/special/TraceCheck.mch"};
		assertEquals(Deadlock, test(a));
	}
	
	
	
}
