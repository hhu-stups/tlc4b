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
		String expected = "---- MODULE test ----\n"
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
				+ "ASSUME Inter({{z}: z \\in {z \\in {1, 2}: 1 = 1}}) = {}\n"
				+ "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testSigma() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES SIGMA(z).(z : {1,2,3}| z+z) = 12 \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals, BBuiltIns\n"
				+ "ASSUME Sigma({z + z : z \\in {1, 2, 3}}) = 12\n"
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testSigma2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES SIGMA(z).(z : {1,2,3} & 1=1| z+z) = 12\n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals, BBuiltIns\n"
				+ "ASSUME Sigma({z + z : z \\in {z \\in {1, 2, 3} : 1 = 1}}) = 12\n"
				+ "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testPi() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES PI(z).(z : {1,2,3}| z+z) = 12 \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals, BBuiltIns\n"
				+ "ASSUME Pi({z + z : z \\in {1, 2, 3}}) = 12\n"
				+ "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testPi2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES PI(z).(z : {1,2,3} & 1=1| z+z) = 12\n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals, BBuiltIns\n"
				+ "ASSUME Pi({z + z : z \\in {z \\in {1, 2, 3} : 1 = 1}}) = 12\n"
				+ "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testSucc() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES succ(3) = 4 \n" + "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME succ[3] = 4\n" + "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testPred() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES pred(2) = 1 \n" + "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME pred[2] = 1\n" + "====";
		compareEquals(expected, machine);
	}

	@Test
	public void testMin() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES min({1}) = 1 \n" + "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME Min({1}) = 1\n" + "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testMax() throws Exception {
		String machine = "MACHINE test\n" + "PROPERTIES max({1}) = 1 \n" + "END";
		String expected = "---- MODULE test ----\n" + "EXTENDS BBuiltIns\n"
				+ "ASSUME Max({1}) = 1\n" + "====";
		compareEquals(expected, machine);
	}
	
	@Test
	public void testMaxInt() throws Exception {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES MAXINT = MAXINT \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "ASSUME 4 = 4\n" + "====";
		compare(expected, machine);
	}

	@Test
	public void testMinInt() throws Exception {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES MININT = MININT \n" + "END";
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers\n"
				+ "ASSUME -1 = -1\n" + "====";
		compare(expected, machine);
	}
	
}
