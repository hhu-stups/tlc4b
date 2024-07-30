package de.tlc4b.tlc.integration.probprivate;

import java.io.File;
import java.util.ArrayList;

import de.tlc4b.TLC4B;
import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.AbstractParseMachineTest;
import de.tlc4b.util.PolySuite;
import de.tlc4b.util.PolySuite.Config;
import de.tlc4b.util.PolySuite.Configuration;

import org.junit.Test;
import org.junit.runner.RunWith;

import tlc2.TLCGlobals;

@RunWith(PolySuite.class)
public class CoverageTest extends AbstractParseMachineTest {

	private final File machine;

	public CoverageTest(File machine, TLCResult result) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		// The subdirectories of the states directory are named after the time when TLC was started.
		// Old versions of TLC (like the one we use) format the time with second precision only,
		// leading to name conflicts when two tests are started within the same second.
		// This line works around the issue by instead using a millisecond timestamp as the name.
		TLCGlobals.metaDir = TLCGlobals.metaRoot + File.separator + System.currentTimeMillis() + File.separator;

		String[] a = new String[] { machine.getPath(), "-notlc" };
		TLC4B.test(a, true);
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<String> list = new ArrayList<>();
		final ArrayList<String> ignoreList = new ArrayList<>();
		list.add("build/prob_examples/public_examples/TLC/");

		list.add("./src/test/resources/");
		ignoreList.add("./src/test/resources/bugs/");
		ignoreList.add("./src/test/resources/compound/");
		ignoreList.add("./src/test/resources/test/");
		return getConfiguration2(list, ignoreList);
	}

}
