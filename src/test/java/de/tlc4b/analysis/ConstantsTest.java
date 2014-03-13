package de.tlc4b.analysis;



import static de.tlc4b.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

public class ConstantsTest {

	@Test
	public void testConstants() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = 1 & k2 : {k} \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "k == 1 \n"
				+ "VARIABLES k2 \n"
				+ "Init == k2 \\in {k} \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<k2>>\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSimpleConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & 1 = 1 \n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ "k == 1 \n"
				+ "ASSUME 1 = 1\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testConstantMultiplePossipleValues() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k  : {1} \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "VARIABLES k \n"
				+ "Init == k \\in {1} \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<k>>\n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testConstantOneValues() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k  = 1 \n" + "END";
		
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testConstantGreaterThan() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k  > 1 \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "k == 2 \n"
				+ "ASSUME k > 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testConstantGreaterThan2() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES 2  > k \n" + "END";
		
		
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "k == 1 \n"
				+ "ASSUME 2 > k \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testScalarParameter() throws Exception {
		String machine = "MACHINE test(t)\n"
				+ "CONSTRAINTS t > 2 \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "t == 3 \n"
				+ "ASSUME t > 2 \n"
				+ "======";
		compare(expected, machine);
	}
	
	
	@Test
	public void testConstants2() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS N \n" 
				+ "PROPERTIES N <: NATURAL & N={1,2,3,4}\n"
				+ "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Naturals\n"
				+ "N == {1,2,3,4}\n"
				+ "ASSUME N \\in SUBSET(Nat) \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testConstants3() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS n\n" 
				+ "PROPERTIES n <: {1,2,3}\n"
				+ "END";
		
		String expected = "---- MODULE test----\n"
				+ "VARIABLES n\n"
				+ "Init == n \\in SUBSET({1, 2, 3})\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<n>>\n"
				+ "======";
		compare(expected, machine);
	}
	
}
