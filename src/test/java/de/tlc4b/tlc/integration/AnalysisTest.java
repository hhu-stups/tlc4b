package de.tlc4b.tlc.integration;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.testString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class AnalysisTest {

	@Test
	public void testDefaultSizes() throws Exception {
		String machine = "MACHINE Test\n"
				+ "SETS S \n"
				+ "DEFINITIONS \n"
				+ "SET_PREF_MININT == 7; \n"
				+ "SET_PREF_MAXINT == 8; \n"
				+ "SET_PREF_DEFAULT_SETSIZE == 9; \n"
				+ "PROPERTIES MININT = 7 & MAXINT = 8 & (1=1 => card(S) = 9)  \n"
				+ "END";
		assertEquals(NoError, testString(machine));
	}
	
	@Test
	public void testMinInt() throws Exception {
		String machine = "MACHINE Test\n"
				+ "SETS S \n"
				+ "DEFINITIONS \n"
				+ "SET_PREF_MININT == 7; \n"
				+ "PROPERTIES MININT = 8  \n"
				+ "END";
		assertEquals(PropertiesError, testString(machine));
	}
	
	@Test
	public void testMaxInt() throws Exception {
		String machine = "MACHINE Test\n"
				+ "SETS S \n"
				+ "DEFINITIONS \n"
				+ "SET_PREF_MAXINT == 7; \n"
				+ "PROPERTIES MAXINT = 8  \n"
				+ "END";
		assertEquals(PropertiesError, testString(machine));
	}
	
	@Test
	public void testDefaultSetSize() throws Exception {
		String machine = "MACHINE Test\n"
				+ "SETS S \n"
				+ "DEFINITIONS \n"
				+ "SET_PREF_DEFAULT_SETSIZE == 9; \n"
				+ "PROPERTIES  (1=1 => card(S) = 10)  \n"
				+ "END";
		assertEquals(PropertiesError, testString(machine));
	}
	
}
