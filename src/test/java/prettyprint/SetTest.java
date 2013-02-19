package prettyprint;

import static org.junit.Assert.*;
import static prettyprint.TestPrinter.compare;

import org.junit.Test;

public class SetTest {

	@Test
	public void testEmptySet() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {} = {} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {} = {}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testSetExtension() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {3,2,1} = {1,2,3} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {3,2,1} = {1,2,3}\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	
	@Test
	public void testSetComprehension() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} = {x | x = 1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {1} = {x \\in {1}: x = 1} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testPowerSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {{},{1}} = POW({1}) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {{},{1}} = SUBSET {1} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testPowerSet1() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = POW1({1,2}) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS BBuiltIns\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k =  POW1({1,2})  \n"
				+ "======";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testCard() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 = card({1,2}) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n" + "EXTENDS FiniteSets\n"
				+ "ASSUME 2 =  Cardinality({1,2})  \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testCartesianProduct() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1}*{2} = {(1,2)} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "ASSUME {1} \\times {2} = {<<1, 2>>}\n"
				+ "====";
		System.out.println(p.result);
		assertEquals(expected, p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testUnion() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} \\/ {2} = {1,2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1} \\cup {2} = {1,2}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2} /\\ {2} = {2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1,2} \\cap {2} = {2}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testDifference() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2} - {2} = {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1,2} \\ {2} = {1}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testElementOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 : {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 \\in {1}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testNotElementOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 /: {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 \\notin {1}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testSubsetEq() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <: {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1} \\subseteq {1}  \n"
				+ "======";
		compare(expected, p.result);
	}
	
	@Test
	public void testStrictSubset() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <<: {1,2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME {1} \\subset {1, 2}\n"
				+ "====";
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testNotSubset() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} /<: {2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME notSubset({1}, {2})\n"
				+ "====";
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testNotStrictSubset() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} /<<: {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME notStrictSubset({1}, {1})\n"
				+ "====";
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testGeneralisedUnion() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES union({{1},{2}}) = {1,2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "ASSUME UNION({{1}, {2}}) = {1, 2}\n"
				+ "====";
		compare(expected, p.result);
	}
	
	@Test
	public void testGeneralisedIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES inter({{1},{1,2}}) = {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME inter({{1}, {1, 2}}) = {1}\n"
				+ "====";
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
}
