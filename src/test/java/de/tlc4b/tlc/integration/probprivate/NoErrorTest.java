package de.tlc4b.tlc.integration.probprivate;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.AbstractParseMachineTest;
import de.tlc4b.util.PolySuite;
import de.tlc4b.util.PolySuite.Config;
import de.tlc4b.util.PolySuite.Configuration;

import org.junit.Test;
import org.junit.runner.RunWith;

import static de.tlc4b.tlc.TLCResults.TLCResult.NoError;
import static de.tlc4b.util.TestUtil.test;
import static org.junit.Assert.assertEquals;

@RunWith(PolySuite.class)
public class NoErrorTest extends AbstractParseMachineTest {

	private final File machine;
	private final TLCResult error;

	public NoErrorTest(File machine, TLCResult result) {
		this.machine = machine;
		this.error = result;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath() };
		assertEquals(error, test(a));
	}

	@Config
	public static Configuration getConfig() {
		List<String> list = new ArrayList<>();
		list.add("build/prob_examples/public_examples/TLC/NoError");
		return getConfiguration(list, NoError);
	}

}
