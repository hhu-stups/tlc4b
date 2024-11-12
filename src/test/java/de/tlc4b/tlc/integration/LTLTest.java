package de.tlc4b.tlc.integration;
/**
 * If the result is not correctly detected in the TLC output, @see de.tlc4b.tlc.TLCResult .
 * */
import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Test;

import de.tlc4b.TLC4BGlobals;
import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.test;

public class LTLTest {

	@BeforeClass
	public static void onlyOnce() {
		TLC4BGlobals.setDeleteOnExit(true);
	}

	@Test
	public void testCounterLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/CounterLTL.mch" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testCounterError() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/CounterError.mch" };
		assertEquals(TemporalPropertyViolation, test(a));
	}

	@Test
	public void testFairnessCounterLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/FairnessCounter.mch" };
		assertEquals(NoError, test(a));
	}

	@Test
	public void testUniversalQuantificaitonLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/UniveralQuatification.mch" };
		assertEquals(TemporalPropertyViolation, test(a));
	}

	@Test
	public void testExistentialQuantificationLTL() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/ExistentialQuantification.mch" };
		assertEquals(NoError, test(a));
	}

	@Test
	public void testFairnessParameter() throws Exception {
		String[] a = new String[] { "src/test/resources/ltl/Fairness_Parameter.mch" };
		assertEquals(NoError, test(a));
	}
	
	@Test
	public void testLTLStatePropertyViolation() throws Exception{
		String[] a = new String[] { "src/test/resources/ltl/StatePropertyViolation.mch" };
		assertEquals(TemporalPropertyViolation, test(a));
	}

}
