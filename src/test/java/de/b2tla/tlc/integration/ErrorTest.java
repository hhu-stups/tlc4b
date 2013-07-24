package de.b2tla.tlc.integration;

import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;
import de.b2tla.tlc.TLCOutput;

public class ErrorTest {

	@BeforeClass
	public static void onlyOnce() {
		B2TLAGlobals.setDeleteOnExit(true);
	}

	@Test
	public void testInvariantError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch" };
		assertEquals(TLCOutput.TLCResult.InvariantViolation, B2TLA.test(a));
	}

	@Test
	public void testDeadlock() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/Deadlock.mch" };
		assertEquals(TLCOutput.TLCResult.Deadlock, B2TLA.test(a));
	}

	@Test
	public void testPropertiesError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/PropertiesError.mch" };
		assertEquals(TLCOutput.TLCResult.PropertiesError, B2TLA.test(a));
	}

	@Test
	public void testNoFile() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoFile.mch" };
		assertEquals(null, B2TLA.test(a));
	}

	@Test
	public void testNoError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/NoError.mch" };
		assertEquals(TLCOutput.TLCResult.NoError, B2TLA.test(a));
	}

	@Test
	public void testEnumerationError() throws Exception {
		String[] a = new String[] { "./src/test/resources/errors/EnumerationError.mch" };
		assertEquals(TLCOutput.TLCResult.TLCError, B2TLA.test(a));
	}

}
