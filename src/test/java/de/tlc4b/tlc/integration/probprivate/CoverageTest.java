package de.tlc4b.tlc.integration.probprivate;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.tlc4b.TLC4B;
import de.tlc4b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import tlc2.TLCGlobals;

@RunWith(Parameterized.class)
public class CoverageTest {
	private final File machine;

	public CoverageTest(File machine) {
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

	@Parameterized.Parameters(name = "{0}")
	public static List<File> data() {
		List<File> machines = new ArrayList<>();
		machines.addAll(TestUtil.getMachinesRecursively("build/prob_examples/public_examples/TLC/"));
		// The subdirectories bugs, compound, and test are intentionally not included here.
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/basics/"));
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/composition/"));
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/errors/"));
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/laws/"));
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/ltl/"));
		machines.addAll(TestUtil.getMachinesRecursively("src/test/resources/special/"));
		return machines;
	}
}
