package de.tlc4b.tlc.integration.probprivate;

import java.io.File;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import static de.tlc4b.util.TestUtil.test;
import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public class NoErrorTest {
	private final File machine;

	public NoErrorTest(File machine) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath() };
		assertEquals(TLCResult.NoError, test(a));
	}

	@Parameterized.Parameters(name = "{0}")
	public static File[] data() {
		return TestUtil.getMachines("build/prob_examples/public_examples/TLC/NoError");
	}
}
