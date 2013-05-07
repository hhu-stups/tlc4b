package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.*;
import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

public class BBuildInsTest {

	
	
	/*
	 * Set BuiltIns
	 */
	
	@Test
	public void testStrictSubset() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES {1} <<: {1,2} \n"
				+ "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME ({1} \\subseteq  {1, 2} /\\ {1} # {1, 2})\n" + "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testNotSubset() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES {1} /<: {2} \n" + "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME notSubset({1}, {2})\n" + "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testPowerSet1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES POW1({1,2}) = {{1}, {2}, {1, 2}} \n" + "END";
		String expected = "---- MODULE test ----\n" 
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME POW1({1, 2}) = {{1}, {2}, {1, 2}}\n" 
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testFin() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES FIN({1,2}) = {{}, {1}, {2}, {1, 2}} \n" + "END";
		String expected = "---- MODULE test ----\n" 
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME FIN({1, 2}) = {{}, {1}, {2}, {1, 2}}\n" 
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testFin1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES FIN1({1,2}) = {{1}, {2}, {1, 2}} \n" + "END";
		String expected = "---- MODULE test ----\n" 
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME FIN1({1, 2}) = {{1}, {2}, {1, 2}}\n" 
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testNotStrictSubset() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} /<<: {1} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME notStrictSubset({1}, {1})\n"
				+ "====";
		assertEquals(expected, translate(machine));
	}

	@Test
	public void testQuantifiedIntersection() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES INTER(z).(z: {1,2} & 1 = 1| {z}) = {} \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME INTER({{z}: z \\in {z \\in {1, 2}: z \\in {1, 2} /\\ 1 = 1}}) = {}\n"
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Ignore
	@Test
	public void testPartialFunction() throws Exception {
		String machine = "MACHINE test\n" + "CONSTANTS k\n"
				+ "PROPERTIES k = {1,2} +-> {1,2}\n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [<<a, b>> \\in { <<a, b>> \\in (Int \\times Int) : a = b} |-> a + b][2, 2]\n"
				+ "====";
		// TODO partial function
		compare(expected, machine);
	}

	// TODO include Standard module BBuiltIns
	@Test
	public void testSigma() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES SIGMA(z).(z : {1,2,3}| z) = 6 \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS BBuiltIns\n"
				+ "ASSUME SIGMA({z : z \\in { z \\in Int : z \\in {1, 2, 3}}}) = 6\n"
				+ "====";
		compareEquals(expected, machine);
	}

	@Ignore
	@Test
	public void testPI() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES PI(z).(z : {1,2,3}| z) = 6 \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME PI() = 1\n" + "======";
		compare(expected, machine);
	}

	@Ignore
	@Test
	public void testSucc() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES succ(3) = 4 \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME succ(3) = 4\n" + "======";
		compareEquals(expected, machine);
	}

	@Ignore
	@Test
	public void testPred() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES pred(2) = 1 \n" + "END";
		String expected = "---- MODULE test----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME pred(2) = 1\n" + "======";
		compare(expected, machine);
	}

	@Ignore
	@Test
	public void testMinInt() throws Exception {
		// TODO read MinInt and MaxInt from Configuration file
	}

	@Ignore
	@Test
	public void testMaxInt() throws Exception {

	}

}
