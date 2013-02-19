package prettyprint;

import static org.junit.Assert.assertEquals;
import static prettyprint.TestPrinter.compare;

import org.junit.Ignore;
import org.junit.Test;

public class MachineParameterTest {

	@Test
	public void testScalarParameterToConstant() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a = 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "ASSUME a = 1\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testScalarParameterToVariable() throws Exception {
		String machine = "MACHINE test(a)\n"
				+ "CONSTRAINTS a : {1,2,3}\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n" 
				+ "VARIABLES a\n"
				+ "Init == a \\in {1,2,3}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testTwoScalarParameter() throws Exception {
		String machine = "MACHINE test(a,b)\n"
				+ "CONSTRAINTS a = 1 & b = 2 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n" 
				+ "a == 1\n"
				+ "b == 2 \n"
				+ "ASSUME a = 1 /\\ b = 2\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Ignore
	@Test
	public void testParameter() throws Exception {
		String machine = "MACHINE test(AA)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n" 
				+ "CONSTANTS AA\n"
				+ "======";
		System.out.println(p.result);
		//TODO include config file: AA
		compare(expected, p.result);
	}
	
	@Test
	public void testMixedParameter() throws Exception {
		String machine = "MACHINE test(a, B)\n"
				+ "CONSTRAINTS a = 1 & card(B)= 2 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS FiniteSets\n"
				+ "CONSTANTS B\n"
				+ "a == 1\n"
				+ "ASSUME a = 1 /\\ Cardinality(B) = 2\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testMixedParameter2() throws Exception {
		String machine = "MACHINE test(a, B)\n"
				+ "CONSTRAINTS a : {1,2} & card(B)= 2 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS FiniteSets\n"
				+ "CONSTANTS B\n"
				+ "VARIABLES a\n"
				+ "Init == a \\in {1, 2} /\\ Cardinality(B) = 2\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
	}
	
}
