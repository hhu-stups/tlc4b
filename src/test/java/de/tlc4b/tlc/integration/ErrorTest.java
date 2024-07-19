package de.tlc4b.tlc.integration;

import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.test;

public class ErrorTest {

	@Test
	public void testTraceValues() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/TraceValues.mch" };
		assertEquals(Deadlock, test(a));
	}
	
	@Test
	public void testInvariantError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch" };
		assertEquals(InvariantViolation, test(a));
	}

	@Test
	public void testDeadlock() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/Deadlock.mch" };
		assertEquals(Deadlock, test(a));
	}

	@Test
	public void testPropertiesError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/PropertiesError.mch" };
		assertEquals(PropertiesError, test(a));
	}

	@Test
	public void testNoFile() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoFile.mch" };
		assertNull(test(a));
	}

	@Test
	public void testNoError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoError.mch" };
		assertEquals(NoError, test(a));
	}

	@Test
	public void testEnumerationError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/EnumerationError.mch" };
		assertEquals(EnumerationError, test(a));
	}
	
	@Test
	public void testAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError.mch" };
		assertEquals(AssertionError, test(a));
	}
	
	
	@Test
	public void testConstantAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError2.mch" };
		assertEquals(AssertionError, test(a));
	}

	@Test
	public void testTemporalPropertyError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/LTLError.mch" };
		assertEquals(TemporalPropertyViolation, test(a));
	}
	
	@Test
	public void testWelldefinednessError1() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError1.mch" };
		assertEquals(WellDefinednessError, test(a));
	}
	
	@Test
	public void testWelldefinednessError2() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError2.mch" };
		assertEquals(WellDefinednessError, test(a));
	}
	
	@Test
	public void testWelldefinednessError3() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError3.mch" };
		assertEquals(WellDefinednessError, test(a));
	}
}
