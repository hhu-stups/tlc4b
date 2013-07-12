 package de.b2tla.tlc.integration;

import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;
import de.b2tla.tlc.TLCOutput;

public class ModulesTest {

	@BeforeClass
	public static void onlyOnce() {
		B2TLAGlobals.setDeleteOnExit(true);
	}
	
	@Test
	public void testRelations() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\RelationsTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testRelations2() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\RelationsTest2.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testFunctions() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\FunctionsTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testFunctionLawsWithLambda() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\FunLawsWithLambda.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}

	@Test
	public void testRelationsVsFunctions() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\RelVsFuncTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testSequences() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\SequencesTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testSequencesExtended() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\SequencesExtendedTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Ignore
	@Test
	public void testSeqLaws() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\SeqLaws.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	@Test
	public void testSeqAsRelations() throws Exception {
		String[] a = new String[] { ".\\src\\test\\resources\\laws\\SequencesAsRelationsTest.mch"};
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	
	
}
