package de.b2tla.tlc.integration;

import static de.b2tla.tlc.TLCOutput.TLCResult.*;
import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;

public class ErrorTest {

	@BeforeClass
	public static void onlyOnce() {
		B2TLAGlobals.setDeleteOnExit(true);
	}

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
	
}
