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
public class InvariantViolationTest extends AbstractParseMachineTest {

	private final File machine;
	private final TLCResult error;

	public InvariantViolationTest(File machine, TLCResult result) {
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
		final ArrayList<TestPair> list = new ArrayList<>();
		list.add(new TestPair(InvariantViolation,
				"build/prob_examples/public_examples/TLC/InvariantViolation"));
		return getConfiguration(list);
	}
}
