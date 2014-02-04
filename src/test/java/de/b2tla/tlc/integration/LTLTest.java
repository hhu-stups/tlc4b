package de.b2tla.tlc.integration;

import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;
import de.b2tla.tlc.TLCOutput;

public class LTLTest {

	@BeforeClass
	public static void onlyOnce() {
		B2TLAGlobals.setDeleteOnExit(true);
	}
	
	@Test
	public void testCounterLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\CounterLTL.mch"};
		//B2TLA.main(a);
		assertEquals(TLCOutput.TLCResult.NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void testFairnessCounterLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\FairnessCounter.mch"};
		//B2TLA.main(a);
		assertEquals(TLCOutput.TLCResult.TemporalPropertyError, B2TLA.test(a,true));
	}
	
	@Test
	public void testUniversalQuantificaitonLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\UniveralQuatification.mch"};
		//B2TLA.main(a);
		assertEquals(TLCOutput.TLCResult.TemporalPropertyError, B2TLA.test(a,true));
	}
	
	@Test
	public void testExistentialQuantificationLTL() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\ExistentialQuantification.mch"};
		//B2TLA.main(a);
		assertEquals(TLCOutput.TLCResult.NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void testFairnessParameter() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\Fairness_Parameter.mch"};
		//B2TLA.main(a);
		assertEquals(TLCOutput.TLCResult.NoError, B2TLA.test(a,true));
	}
	
}
