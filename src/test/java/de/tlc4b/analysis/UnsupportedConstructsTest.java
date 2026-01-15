package de.tlc4b.analysis;

import de.tlc4b.exceptions.NotSupportedException;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class UnsupportedConstructsTest {

	@Test(expected = NotSupportedException.class)
	public void testExtends() throws Exception {
		final String machine = "MACHINE test\n" + "EXTENDS foo\n PROMOTES bar\n" + "END";
		TestUtil.translate(machine);
	}

	@Test(expected = NotSupportedException.class)
	public void testImplementation() throws Exception {
		final String machine = "IMPLEMENTATION test REFINES foo END";
		TestUtil.translate(machine);
	}

	@Test(expected = NotSupportedException.class)
	public void testFreetypes() throws Exception {
		final String machine = "MACHINE M FREETYPES F = F1, F2(INTEGER) END";
		TestUtil.translate(machine);
	}
}
