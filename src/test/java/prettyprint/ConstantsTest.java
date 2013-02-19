package prettyprint;

import static prettyprint.TestPrinter.compare;


import org.junit.Test;

public class ConstantsTest {

	@Test
	public void testConstants() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = 1 & k2 : {k} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		System.out.println(p.result);
		
		String expected = "---- MODULE test----\n"
				+ "k == 1 \n"
				+ "VARIABLES k2 \n"
				+ "Init == k = 1 /\\ k2 \\in {k} \n"
				+ "======";
		compare(expected, p.result);
	}
	
	
	@Test
	public void testConstantMultiplePossipleValues() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k  : {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "VARIABLES k \n"
				+ "Init == k \\in {1} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testConstantOneValues() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k  = 1 \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
}
