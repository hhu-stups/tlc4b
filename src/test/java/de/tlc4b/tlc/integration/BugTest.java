package de.tlc4b.tlc.integration;

import org.junit.Test;

import de.tlc4b.TLC4B;

public class BugTest {

	@Test
	public void testTraceValues() {
		String[] a = new String[] { "./src/test/resources/bugs/LTLParseError.mch" };
		TLC4B.main(a);
	}

}