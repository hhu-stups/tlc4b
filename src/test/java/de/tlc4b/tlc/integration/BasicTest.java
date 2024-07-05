package de.tlc4b.tlc.integration;

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
import static de.tlc4b.tlc.TLCResults.TLCResult.NoError;
import static de.tlc4b.util.TestUtil.test;

@RunWith(PolySuite.class)
public class BasicTest extends AbstractParseMachineTest {

	private final File machine;
	private final TLCResult error;

	public BasicTest(File machine, TLCResult result) {
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
		list.add(new TestPair(NoError, "./src/test/resources/composition/sees"));
		list.add(new TestPair(NoError, "./src/test/resources/composition/sees2"));
		list.add(new TestPair(NoError, "./src/test/resources/basics"));
		list.add(new TestPair(NoError, "./src/test/resources/laws"));
		return getConfiguration(list);
	}
}
