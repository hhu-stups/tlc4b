package de.tlc4b.tlc.integration;

import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class ErrorTest {

	@Test
	public void testTraceValues() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/TraceValues.mch" };
		assertEquals(TLCResults.TLCResult.Deadlock, TestUtil.test(a));
	}
	
	@Test
	public void testInvariantError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch" };
		assertEquals(TLCResults.TLCResult.InvariantViolation, TestUtil.test(a));
	}

	@Test
	public void testDeadlock() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/Deadlock.mch" };
		assertEquals(TLCResults.TLCResult.Deadlock, TestUtil.test(a));
	}

	@Test
	public void testPropertiesError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/PropertiesError.mch" };
		assertEquals(TLCResults.TLCResult.PropertiesError, TestUtil.test(a));
	}

	@Test
	public void testNoFile() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoFile.mch" };
		assertNull(TestUtil.test(a));
	}

	@Test
	public void testNoError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoError.mch" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}

	@Test
	public void testEnumerationError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/EnumerationError.mch" };
		assertEquals(TLCResults.TLCResult.EnumerationError, TestUtil.test(a));
	}
	
	@Test
	public void testAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError.mch" };
		assertEquals(TLCResults.TLCResult.AssertionError, TestUtil.test(a));
	}
	
	
	@Test
	public void testConstantAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError2.mch" };
		assertEquals(TLCResults.TLCResult.AssertionError, TestUtil.test(a));
	}

	@Test
	public void testTemporalPropertyError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/LTLError.mch" };
		assertEquals(TLCResults.TLCResult.TemporalPropertyViolation, TestUtil.test(a));
	}
	
	@Test
	public void testWelldefinednessError1() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError1.mch" };
		assertEquals(TLCResults.TLCResult.WellDefinednessError, TestUtil.test(a));
	}
	
	@Test
	public void testWelldefinednessError2() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError2.mch" };
		assertEquals(TLCResults.TLCResult.WellDefinednessError, TestUtil.test(a));
	}
	
	@Test
	public void testWelldefinednessError3() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError3.mch" };
		assertEquals(TLCResults.TLCResult.WellDefinednessError, TestUtil.test(a));
	}
}
