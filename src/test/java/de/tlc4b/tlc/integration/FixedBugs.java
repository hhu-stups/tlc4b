package de.tlc4b.tlc.integration;

import static de.tlc4b.tlc.TLCResults.TLCResult.*;
import static de.tlc4b.util.TestUtil.testString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;


public class FixedBugs {

	@Test
	public void testFunctionAssignment() throws Exception {
		String machine = 
				"MACHINE Test\n"
				+ "VARIABLES x \n"
				+ "INVARIANT x : 1..3 +-> 1..2 \n"
				+ "INITIALISATION x := {} \n"
				+ "OPERATIONS foo = PRE x = {} THEN x(1) := 2 END \n"
				+ "END";
		assertEquals(Deadlock, testString(machine));
	}
}
