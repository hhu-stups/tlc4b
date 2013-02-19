package prettyprint;

import static prettyprint.TestPrinter.compare;

import org.junit.Ignore;
import org.junit.Test;

public class NumbersTest {

	
	@Test
	public void testInteger() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INTEGER = INTEGER\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME Int = Int\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testNatural() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NATURAL = NATURAL\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat = Nat\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testNatural1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NATURAL1 = NATURAL1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat \\ {0} = Nat \\ {0}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testInt() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INT = INT\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME Int = Int\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testNat() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NAT = NAT\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat = Nat\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testNat1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES NAT1 = NAT1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME Nat \\ {0} = Nat \\ {0}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testInterval() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2,3} = 1..3\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME {1,2,3} = 1..3\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Ignore
	@Test
	public void testMinInt() throws Exception {
		//TODO read MinInt and MaxInt from Configuration file
	}
	
	@Ignore
	@Test
	public void testMaxInt() throws Exception {

	}
	
	@Test
	public void testGreaterThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 > 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 2 > 1\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testLessThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 < 2\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 < 2\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testGreaterThanEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 >= 2\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 >= 2\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	
	@Test
	public void testLessThanEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 <= 2\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME 1 =< 2\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testMin() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = min({1,2,3})\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = CHOOSE min \\in {1,2,3}: \\A p \\in {1,2,3}: min =< p \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testMax() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 3 = max({1,2,3})\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 3 = CHOOSE max \\in {1,2,3}: \\A p \\in {1,2,3}: max >= p \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	
	@Test
	public void testAdd() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 = 1 + 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 2 = 1 + 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testMinus() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 2 - 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 2 - 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testMult() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 * 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 * 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testDiv() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 / 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 \\div 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testPower() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = 1 ** 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 = 1 ^ 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testModulo() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 0 = 1 mod 1\n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 0 = 1 % 1 \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	
	@Test
	public void testUnaryMinus() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES -1 = 1  \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME -1 = 1\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	
	//TODO include Standard module BBuiltIns
	@Test
	public void testSigma() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES SIGMA(z).(z : {1,2,3}| z) = 6 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME SIGMA({z: z \\in {z \\in Int: z \\in {1,2,3} }} = 6)\n"
				+ "======";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testPI() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES PI(z).(z : {1,2,3}| z) = 6 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME PI() = 1\n"
				+ "======";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testSucc() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES succ(3) = 4 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME succ(3) = 4\n"
				+ "======";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	
	@Test
	public void testPred() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES pred(2) = 1 \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME pred(2) = 1\n"
				+ "======";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	
}
