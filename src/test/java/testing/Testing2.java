package testing;

import static de.tlc4b.tlc.TLCResults.TLCResult.NoError;
import static de.tlc4b.util.TestUtil.test;

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
public class Testing2 extends AbstractParseMachineTest {

	private final File machine;

	public Testing2(File machine, TLCResult result) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] {
				machine.getPath()};
		TLC4B.main(a);
		//TLC4B.test(a,false);
		//test(a);
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<TestPair> list = new ArrayList<TestPair>();
		list.add(new TestPair(NoError, "./src/test/resources/testing"));
		return getConfiguration(list);
	}

}
