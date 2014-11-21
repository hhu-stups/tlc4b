package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.checkMachine;

import org.junit.Test;

import de.tlc4b.exceptions.NotSupportedException;

public class NotSupportedTest {

	@Test(expected = NotSupportedException.class)
	public void testDuplicateSeenMachine() throws Exception {
		String machine = "MACHINE test \n" + "SEES M1 \n" + "END";
		checkMachine(machine);
	}
}
