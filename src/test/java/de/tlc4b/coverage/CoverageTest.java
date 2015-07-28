package de.tlc4b.coverage;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.tlc4b.TLC4B;
import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.AbstractParseMachineTest;
import de.tlc4b.util.PolySuite;
import de.tlc4b.util.PolySuite.Config;
import de.tlc4b.util.PolySuite.Configuration;

@RunWith(PolySuite.class)
public class CoverageTest extends AbstractParseMachineTest {

	private final File machine;

	public CoverageTest(File machine, TLCResult result) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath(), "-notlc" };
		TLC4B.test(a, true);
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<String> list = new ArrayList<String>();
		final ArrayList<String> ignoreList = new ArrayList<String>();
		list.add("../prob_examples/public_examples/TLC/");

		list.add("./src/test/resources/");
		ignoreList.add("./src/test/resources/compound/");
		ignoreList.add("./src/test/resources/other/");
		ignoreList.add("./src/test/resources/test/");
		ignoreList.add("./src/test/resources/testing/");
		ignoreList.add("./src/test/resources/todo/");
		ignoreList.add("./src/test/resources/bugs/");
		return getConfiguration2(list, ignoreList);
	}

}
