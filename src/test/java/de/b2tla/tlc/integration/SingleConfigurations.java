package de.b2tla.tlc.integration;

import static de.b2tla.tlc.TLCOutput.TLCResult.NoError;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;

public class SingleConfigurations {

	
	@Test
	public void TautologiesPl() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/others/TautologiesPL.mch", "-nodead"};
		assertEquals(NoError, B2TLA.test(a));
	}

}
