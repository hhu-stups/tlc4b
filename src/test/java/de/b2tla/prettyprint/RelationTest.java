package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;
import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import de.b2tla.B2TLA;

public class RelationTest {

	
	@Test
	public void testCouple() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2) = (1|->2) \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME <<1,2>> = <<1,2>>\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testCouple3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2,3) = ((1,2),3) \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME <<<<1, 2>>, 3>> = <<<<1, 2>>, 3>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testCouple4() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2,3,4) = (((1,2),3),4) \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME <<<<<<1, 2>>, 3>>, 4>> = <<<<<<1, 2>>, 3>>, 4>>\n"
				+ "====";
		compare(expected, machine);
	}
	
}
