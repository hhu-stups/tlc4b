package de.b2tla.tlc.integration;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.tlc.TLCOutput;

public class LTLTest {

	@Test
	public void testRelations() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\ltl\\CounterLTL.mch"};
		B2TLA.main(a);
		//assertEquals(TLCOutput.ERROR.TemporalProperty, B2TLA.test(a));
	}
	
}
