package prettyprint;

import static org.junit.Assert.*;
import static prettyprint.TestPrinter.*;

import org.junit.Ignore;
import org.junit.Test;



public class FunctionTest {

	@Test
	public void testLambdaAbstraction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES [1] = %x.(x = 1 | 1)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME <<1>> = [x \\in { x \\in {1} : x = 1} |-> 1 ]\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
		
	}
	
	@Test
	public void testFunctionApplication() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = %x.(x = 1 | 1)(1)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 = [x \\in { x \\in {1} : x = 1} |-> 1 ][1]\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testFunctionApplicationMoreArguments() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 4 = %a,b.(a=b | a+b)(2,2)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME 4 = [<<a, b>> \\in { <<a, b>> \\in (Int \\times Int) : a = b} |-> a + b][2, 2]\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
		//compare(expected, p.result);
	}
	
	@Ignore
	@Test
	public void testPartialFunction() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k\n"
				+ "PROPERTIES k = {1,2} +-> {1,2}\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [<<a, b>> \\in { <<a, b>> \\in (Int \\times Int) : a = b} |-> a + b][2, 2]\n"
				+ "====";
		System.out.println(p.result);
		//TODO partial function
		assertEquals(expected, p.result);
		//compare(expected, p.result);
	}
	
	
	
	@Test
	public void testFunctionVsRelation() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {(1|->1)} = %x.(x = 1 | 1)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME {<<1,1>>} = {<<x, 1>> : x \\in { x \\in {1} : x = 1}}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}

	@Test
	public void testFunctionVsRelation2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {(1|->2|->3)} = %a,b.(a = b | a+b)\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME {<<<<1, 2>>, 3>>} = {<<<<a, b>>, a + b>> : <<a, b>> \\in { <<a, b>> \\in (Int \\times Int) : a = b}}\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
		// The TLA2B translator does not support nested tuples yet.
		//compare(expected, p.result);
	}

	@Test
	public void testDomain() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} = dom(%x.(x = 1 | 1))\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1} = DOMAIN [x \\in { x \\in {1} : x = 1} |-> 1 ]\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testRange() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES ran(%x.(x = 1 | 1)) = {1}\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME ran([x \\in { x \\in {1} : x = 1} |-> 1]) = {1}\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
		//compare(expected, p.result);
	}
	

}
