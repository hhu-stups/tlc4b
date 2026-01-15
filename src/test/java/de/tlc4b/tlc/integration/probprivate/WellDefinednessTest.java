package de.tlc4b.tlc.integration.probprivate;

import java.io.File;

import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public class WellDefinednessTest {
	private final File machine;

	public WellDefinednessTest(File machine) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath(), "-wdcheck" };
		assertEquals(TLCResults.TLCResult.WellDefinednessError, TestUtil.test(a));
	}

	@Parameterized.Parameters(name = "{0}")
	public static File[] data() {
		return TestUtil.getMachines("build/prob_examples/public_examples/TLC/WellDefinednessError");
	}
}
