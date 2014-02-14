package de.b2tla.tlc.integration;

import static de.b2tla.tlc.TLCOutput.TLCResult.*;
import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

import de.b2tla.B2TLA;

public class ErrorTest {

	@Test
	public void testInvariantError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch" };
		assertEquals(InvariantViolation, B2TLA.test(a,true));
	}

	@Test
	public void testDeadlock() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/Deadlock.mch" };
		assertEquals(Deadlock, B2TLA.test(a,true));
	}

	@Test
	public void testPropertiesError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/PropertiesError.mch" };
		assertEquals(PropertiesError, B2TLA.test(a,true));
	}

	@Test
	public void testNoFile() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoFile.mch" };
		assertEquals(null, B2TLA.test(a,true));
	}

	@Test
	public void testNoError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoError.mch" };
		assertEquals(NoError, B2TLA.test(a,true));
	}

	@Test
	public void testEnumerationError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/EnumerationError.mch" };
		assertEquals(TLCError, B2TLA.test(a,true));
	}
	
	@Test
	public void testAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError.mch" };
		assertEquals(AssertionError, B2TLA.test(a,true));
	}
	
	
	@Test
	public void testConstantAssertionError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/AssertionError2.mch" };
		assertEquals(AssertionError, B2TLA.test(a,true));
	}

	@Test
	public void testTemporalPropertyError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/LTLError.mch" };
		assertEquals(TemporalPropertyError, B2TLA.test(a,true));
	}
	
	@Test
	public void testWelldefinednessError1() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError1.mch" };
		assertEquals(WellDefinednessError, B2TLA.test(a,true));
	}
	
	@Test
	public void testWelldefinednessError2() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError2.mch" };
		assertEquals(WellDefinednessError, B2TLA.test(a,true));
	}
	
	@Test
	public void testWelldefinednessError3() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WelldefinednessError3.mch" };
		assertEquals(WellDefinednessError, B2TLA.test(a,true));
	}
	
	@Ignore
	@Test
	public void testWellDefinednessErrorFunctionAssignment() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/WellDefinednessErrorFunctionAssignment.mch" };
		assertEquals(WellDefinednessError, B2TLA.test(a,true));
	}
	
}
