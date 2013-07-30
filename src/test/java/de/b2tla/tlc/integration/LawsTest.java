package de.b2tla.tlc.integration;

import static de.b2tla.tlc.TLCOutput.TLCResult.*;
import static org.junit.Assert.assertEquals;


import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;

public class LawsTest {

	@Test
	public void BoolLaws() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/BoolLaws.mch"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void BoolWithArithLaws() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/BoolWithArithLaws.mch", "-nodead"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void FunLaws() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/FunLaws.mch"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void FunLawsWithLambda() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/FunLawsWithLambda.mch"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void RelLaws_TLC() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/RelLaws_TLC.mch"};
		assertEquals(Goal, B2TLA.test(a,true));
	}
	
	@Test
	public void BoolLaws_SetCompr() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/BoolLaws_SetCompr.mch"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void BoolLaws_SetComprCLPFD() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/BoolLaws_SetComprCLPFD.mch"};
		assertEquals(NoError, B2TLA.test(a,true));
	}

	@Test
	public void CardinalityLaws_TLC() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/CardinalityLaws_TLC.mch", "-nodead"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void EqualityLaws() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/EqualityLaws.mch", "-nodead"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
	
	@Test
	public void SubsetLaws() throws Exception {
		B2TLAGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "../probprivate/public_examples/TLC/Laws/SubsetLaws.mch", "-nodead"};
		assertEquals(NoError, B2TLA.test(a,true));
	}
}
