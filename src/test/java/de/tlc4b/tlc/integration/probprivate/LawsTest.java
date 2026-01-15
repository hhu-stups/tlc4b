package de.tlc4b.tlc.integration.probprivate;

import de.tlc4b.TLC4BGlobals;
import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class LawsTest {

	@Test
	public void BoolLaws() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/BoolLaws.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void BoolWithArithLaws() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/BoolWithArithLaws.mch", "-nodead"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void FunLaws() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/FunLaws.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void FunLawsWithLambda() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/FunLawsWithLambda.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void RelLaws_TLC() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/RelLaws_TLC.mch"};
		assertEquals(TLCResults.TLCResult.Goal, TestUtil.test(a));
	}
	
	@Test
	public void BoolLaws_SetCompr() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/BoolLaws_SetCompr.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void BoolLaws_SetComprCLPFD() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/BoolLaws_SetComprCLPFD.mch"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}

	@Test
	public void CardinalityLaws_TLC() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/CardinalityLaws_TLC.mch", "-nodead"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void EqualityLaws() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/EqualityLaws.mch", "-nodead"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
	
	@Test
	public void SubsetLaws() throws Exception {
		TLC4BGlobals.setDeleteOnExit(true);
		String[] a = new String[] { "build/prob_examples/public_examples/TLC/Laws/SubsetLaws.mch", "-nodead"};
		assertEquals(TLCResults.TLCResult.NoError, TestUtil.test(a));
	}
}
