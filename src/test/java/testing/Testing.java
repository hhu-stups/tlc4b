package testing;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.tlc4b.TLC4B;
import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.AbstractParseMachineTest;
import de.tlc4b.util.PolySuite;
import de.tlc4b.util.TestPair;
import de.tlc4b.util.PolySuite.Config;
import de.tlc4b.util.PolySuite.Configuration;



@RunWith(PolySuite.class)
public class Testing extends AbstractParseMachineTest{

	
	private final File machine;
	private final TLCResult error;

	public Testing(File machine, TLCResult result) {
		this.machine = machine;
		this.error = result;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath()};
		//B2TLA.main(a);
		//assertEquals(error, B2TLA.test(a,false));
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<TestPair> list = new ArrayList<TestPair>();
		list.add(new TestPair(NoError, "./src/test/resources/Testing"));
		return getConfiguration(list);
	}
}