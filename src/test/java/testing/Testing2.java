package testing;


import static de.b2tla.tlc.TLCResults.TLCResult.NoError;
import static org.junit.Assert.*;
import static de.b2tla.util.TestUtil.test;
import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.b2tla.B2TLA;
import de.b2tla.tlc.TLCResults.TLCResult;
import de.b2tla.util.AbstractParseMachineTest;
import de.b2tla.util.PolySuite;
import de.b2tla.util.TestPair;
import de.b2tla.util.PolySuite.Config;
import de.b2tla.util.PolySuite.Configuration;

@RunWith(PolySuite.class)
public class Testing2 extends AbstractParseMachineTest{
		
	private final File machine;
	private final TLCResult error;

	public Testing2(File machine, TLCResult result) {
		this.machine = machine;
		this.error = result;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] {machine.getPath()};
		
		B2TLA.main(a);
		//B2TLA.test(a,true);
		//test(a);
		//assertEquals(error, B2TLA.test(a,true));
		//assertEquals(1,2);
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<TestPair> list = new ArrayList<TestPair>();
		list.add(new TestPair(NoError, "./src/test/resources/testing"));
		return getConfiguration(list);
	}
	
//	@Test
//	public void testInvariantError() throws Exception {
//		String[] a = new String[] { "./src/test/resources/laws/RelationsTest.mch", "-tmp" };
//		B2TLA.main(a);
//	}
	
//	@Test
//	public void testInvariantError() throws Exception {
//		String[] a = new String[] { "./src/test/resources/errors/InvariantError.mch" };
//		assertEquals(InvariantViolation, B2TLA.test(a,false));
//	}
}
