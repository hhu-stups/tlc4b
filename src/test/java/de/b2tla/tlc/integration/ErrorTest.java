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
		String[] a = new String[] { ".\\src\\test\\resources\\error\\InvariantError.mch" };
		assertEquals(TLCOutput.ERROR.Invariant, B2TLA.test(a));
	}

	@Test
	public void testDeadlock() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\error\\Deadlock.mch" };
		assertEquals(TLCOutput.ERROR.Deadlock, B2TLA.test(a));
	}

	@Test
	public void testPropertiesError() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\error\\PropertiesError.mch" };
		assertEquals(TLCOutput.ERROR.PropertiesError, B2TLA.test(a));
	}

	@Test
	public void testNoFile() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\error\\NoFile.mch" };
		assertEquals(null, B2TLA.test(a));
	}

	@Test
	public void testNoError() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\error\\NoError.mch" };
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}

	@Test
	public void testEnumerationError() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\error\\EnumerationError.mch" };
		assertEquals(TLCOutput.ERROR.TLCError, B2TLA.test(a));
	}

}
