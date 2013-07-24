package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;
import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

public class SetTest {

	@Test
	public void testEmptySet() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {} = {} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {} = {}\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetExtension() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {3,2,1} = {1,2,3} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {3,2,1} = {1,2,3}\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} = {x | x = 1} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {1} = {x \\in {1}: TRUE} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} = {x | x = 1 & 1 = 1} \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {1} = {x \\in {1}: 1 = 1 } \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testSetComprehension3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,TRUE,2) : {a,b,c | (a,b,c) : {1} * {TRUE} * {2} } \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {1} = {x \\in {1}: 1 = 1 } \n"
				+ "======";
	}
	
	
	@Test
	public void testPowerSet() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {{},{1}} = POW({1}) \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME {{},{1}} = SUBSET {1} \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testCard() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 2 = card({1,2}) \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS FiniteSets\n"
				+ "ASSUME 2 =  Cardinality({1,2})  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testCartesianProduct() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1}*{2} = {(1,2)} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME {1} \\times {2} = {<<1, 2>>}\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testCartesianProduct2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1}*{2}*{3} = {(1,2,3)} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME ({1} \\times {2}) \\times {3} = {<<<<1, 2>>, 3>>}\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testUnion() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} \\/ {2} = {1,2} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1} \\cup {2} = {1,2}  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2} /\\ {2} = {2} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1,2} \\cap {2} = {2}  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetSubstraction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2} \\ {2} = {1} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME {1,2} \\ {2} = {1}\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testDifference() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1,2} - {2} = {1} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1,2} \\ {2} = {1}  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testElementOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 : {1} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 \\in {1}  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testNotElementOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 /: {1} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME 1 \\notin {1}  \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSubsetEq() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <: {1} \n" + "END";
		String expected = "---- MODULE test----\n"
				+ "ASSUME {1} \\in SUBSET({1})  \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testGeneralisedUnion() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES union({{1},{2}}) = {1,2} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME Union({{1}, {2}}) = {1, 2}\n"
				+ "====";
		assertEquals(expected, translate(machine));
	}
	
	
	@Test
	public void testGeneralisedIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES inter({{1},{1,2}}) = {1} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME Inter({{1}, {1, 2}}) = {1}\n"
				+ "====";
		assertEquals(expected, translate(machine));
	}
	
	@Test
	public void testQuantifiedUnion() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES UNION(z).(z: {1,2} & 1 = 1| {z}) = {1,2} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME Union({{z}: z \\in {z \\in ({1, 2}): 1 = 1}}) = {1, 2}\n"
				+ "====";
		//TODO ERROR in TLA2B
		compareEquals(expected, machine);
	}
	
	@Test
	public void testQuantifiedIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INTER(z).(z: {1,2} & 1 = 1| {z}) = {} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME Inter({{z}: z \\in {z \\in ({1, 2}): 1 = 1}}) = {}\n"
				+ "====";
		System.out.println(expected);
		compareEquals(expected, machine);
	}
	
}
