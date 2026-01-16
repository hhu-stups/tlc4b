package de.tlc4b.exceptions;

import de.tlc4b.util.TestUtil;

import org.junit.Test;

public class DefinitionsAnalyserTest {

	
	
	@Test (expected = TranslationException.class)
	public void testMaxIntException() throws Exception {
		String machine = "MACHINE test\n" 
				+ "DEFINITIONS SET_PREF_MAXINT == TRUE; \n" 
				+ "END";
		TestUtil.checkMachine(machine);
	}
	
	@Test (expected = TranslationException.class)
	public void testMinIntException() throws Exception {
		String machine = "MACHINE test\n" 
				+ "DEFINITIONS SET_PREF_MININT == TRUE; \n" 
				+ "END";
		TestUtil.checkMachine(machine);
	}
	
	@Test (expected = TranslationException.class)
	public void testDefaultSetSizeException() throws Exception {
		String machine = "MACHINE test\n" 
				+ "DEFINITIONS SET_PREF_DEFAULT_SETSIZE == TRUE; \n" 
				+ "END";
		TestUtil.checkMachine(machine);
	}
	
}
