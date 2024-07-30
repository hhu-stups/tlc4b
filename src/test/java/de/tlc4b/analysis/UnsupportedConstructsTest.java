package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.*;

import org.junit.Test;

import de.tlc4b.exceptions.NotSupportedException;

public class UnsupportedConstructsTest {

	@Test(expected = NotSupportedException.class)
	public void testExtends() throws Exception {
		final String machine = "MACHINE test\n" + "EXTENDS foo\n PROMOTES bar\n" + "END";
		translate(machine);
	}

	@Test(expected = NotSupportedException.class)
	public void testImplementation() throws Exception {
		final String machine = "IMPLEMENTATION test REFINES foo END";
		translate(machine);
	}
}
