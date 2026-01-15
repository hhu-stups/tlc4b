package de.tlc4b.tlc.integration;

import de.tlc4b.TLC4BGlobals;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.BeforeClass;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * If the result is not correctly detected in the TLC output, @see de.tlc4b.tlc.TLCResult .
 */
public class LTLTest {

	@BeforeClass
	public static void onlyOnce() {
		TLC4BGlobals.setDeleteOnExit(true);
	}

	@Test
	public void testCounterLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/CounterLTL.mch" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testCounterError() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/CounterError.mch" };
		assertEquals(TLCResults.TLCResult.TemporalPropertyViolation, TestUtil.test(a));
	}

	@Test
	public void testFairnessCounterLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/FairnessCounter.mch" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}

	@Test
	public void testUniversalQuantificaitonLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/UniveralQuatification.mch" };
		assertEquals(TLCResults.TLCResult.TemporalPropertyViolation, TestUtil.test(a));
	}

	@Test
	public void testExistentialQuantificationLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/ExistentialQuantification.mch" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}

	@Test
	public void testFairnessParameter() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/Fairness_Parameter.mch" };
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void testLTLStatePropertyViolation() throws Exception{
		String[] a = new String[] { "src/test/resources/ltl/StatePropertyViolation.mch" };
		assertEquals(TLCResults.TLCResult.TemporalPropertyViolation, TestUtil.test(a));
	}

}
