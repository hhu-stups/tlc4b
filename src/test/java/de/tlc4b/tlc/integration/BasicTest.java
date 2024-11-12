package de.tlc4b.tlc.integration;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import static de.tlc4b.TLC4BOption.DFID;
import static de.tlc4b.util.TestUtil.test;
import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public class BasicTest {
	private final File machine;

	public BasicTest(File machine) {
		this.machine = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] { machine.getPath() };
		assertEquals(TLCResult.NoError, test(a));
	}

	@Test
	public void testRunTLCDFS() throws Exception {
		String[] a = new String[] { machine.getPath(), DFID.cliArg(), "20" };
		assertEquals(TLCResult.NoError, test(a));
	}

	@Parameterized.Parameters(name = "{0}")
	public static List<File> data() {
		List<File> machines = new ArrayList<>();
		machines.addAll(Arrays.asList(TestUtil.getMachines("./src/test/resources/composition/sees")));
		machines.addAll(Arrays.asList(TestUtil.getMachines("./src/test/resources/composition/sees2")));
		machines.addAll(Arrays.asList(TestUtil.getMachines("./src/test/resources/basics")));
		machines.addAll(Arrays.asList(TestUtil.getMachines("./src/test/resources/laws")));
		return machines;
	}
}
