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

	@Test(expected = NotSupportedException.class)
	public void testFreetypes() throws Exception {
		final String machine = "MACHINE M FREETYPES F = F1, F2(INTEGER) END";
		translate(machine);
	}

	@Test(expected = NotSupportedException.class)
	public void testLetExpr() throws Exception {
		final String machine = "MACHINE M VARIABLES x INVARIANT x : INTEGER INITIALISATION x := (LET foo BE foo=42 IN foo END) END";
		translate(machine);
	}

	@Test(expected = NotSupportedException.class)
	public void testLetPred() throws Exception {
		final String machine = "MACHINE M VARIABLES x INVARIANT x : INTEGER INITIALISATION x : (LET foo BE foo=42 IN x=foo END) END";
		translate(machine);
	}
}
