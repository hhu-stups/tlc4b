package de.tlc4b.tlc.integration.probprivate;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.test;
import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.AbstractParseMachineTest;
import de.tlc4b.util.PolySuite;
import de.tlc4b.util.TestPair;
import de.tlc4b.util.PolySuite.Config;
import de.tlc4b.util.PolySuite.Configuration;

@RunWith(PolySuite.class)
public class DeadlockTest extends AbstractParseMachineTest {

	private final File machine;
	private final TLCResult error;

	public DeadlockTest(File machine, TLCResult result) {
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
		final ArrayList<TestPair> list = new ArrayList<TestPair>();
		list.add(new TestPair(Deadlock,
				"build/prob_examples/public_examples/TLC/Deadlock"));
		return getConfiguration(list);
	}
}
