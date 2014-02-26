package de.b2tla.tlc.integration;

import static org.junit.Assert.assertEquals;
import static de.b2tla.tlc.TLCResults.TLCResult.*;
import org.junit.BeforeClass;
import org.junit.Test;

import de.b2tla.B2TLAGlobals;
import static de.b2tla.util.TestUtil.test;

public class LTLTest {

	@BeforeClass
	public static void onlyOnce() {
		B2TLAGlobals.setDeleteOnExit(true);
	}

	@Test
	public void testCounterLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\CounterLTL.mch" };
		assertEquals(NoError, test(a));
	}

	@Test
	public void testFairnessCounterLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\FairnessCounter.mch" };
		assertEquals(TemporalPropertyError, test(a));
	}

	@Test
	public void testUniversalQuantificaitonLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\UniveralQuatification.mch" };
		assertEquals(TemporalPropertyError, test(a));
	}

	@Test
	public void testExistentialQuantificationLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\ExistentialQuantification.mch" };
		assertEquals(NoError, test(a));
	}

	@Test
	public void testFairnessParameter() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\Fairness_Parameter.mch" };
		assertEquals(NoError, test(a));
	}

}
