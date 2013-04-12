package de.b2tla.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;

public class ModelValuesTest {

	@Test
	public void testEnumeratedSet() throws BException {
		String machine = "MACHINE test\n" 
				+ "SETS S = {a,b}"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = a \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		System.out.println(t.constants.get("k").toString());
		assertEquals("S", t.constants.get("k").toString());
	}
	
	@Test
	public void testEnumeratedSet1() throws BException {
		String machine = "MACHINE test\n" 
				+ "SETS S = {a,b}"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = S \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(S)", t.constants.get("k").toString());
	}
}
