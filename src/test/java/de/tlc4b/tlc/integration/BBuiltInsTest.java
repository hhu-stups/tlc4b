package de.tlc4b.tlc.integration;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.testString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class BBuiltInsTest {

	@Test
	public void testIntersectionWDError() throws Exception {
		String machine = "MACHINE Test\n" + "PROPERTIES \n"
				+ "inter({}) = {} \n" + "END";
		assertEquals(WellDefinednessError, testString(machine));
	}
}
