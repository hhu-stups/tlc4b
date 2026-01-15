package de.tlc4b.tlc.integration;

import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.TestUtil;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class BBuiltInsTest {

	@Test
	public void testIntersectionWDError() throws Exception {
		String machine = "MACHINE Test\n" + "PROPERTIES \n"
				+ "inter({}) = {} \n" + "END";
		assertEquals(TLCResults.TLCResult.WellDefinednessError, TestUtil.testString(machine));
	}
}
