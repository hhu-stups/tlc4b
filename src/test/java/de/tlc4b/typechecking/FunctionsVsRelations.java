package de.tlc4b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;

public class FunctionsVsRelations {

	@Test
	public void testCardFunction() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k =  %x.(x : {1} | 1) & card(k) = 1 \n"
				+ "END";
		TestTypechecker t =  new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
	}
}
