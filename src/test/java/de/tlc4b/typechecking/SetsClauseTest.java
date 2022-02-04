package de.tlc4b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;

public class SetsClauseTest {

	
	@Test
	public void testDeferredSet() throws BException {
		String machine = "MACHINE test\n" 
				+ "SETS DEF \n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k : DEF \n" 
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("DEF", t.constants.get("k").toString());
	}
	
	@Ignore
	@Test
	public void testDeferredSet2() throws BException {
		String machine = "MACHINE test(DEF)\n" 
				+ "CONSTANTS k \n"
				+ "PROPERTIES k : DEF \n" 
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("DEF", t.constants.get("k").toString());
	}
	
}
