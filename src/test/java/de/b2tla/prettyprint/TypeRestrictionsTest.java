package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

public class TypeRestrictionsTest {
	@Test
	public void testSetComprehensionEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x = 1}\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k == {x \\in {1}: x  = 1} \n"
				+ "ASSUME k = {x \\in {1}: x = 1} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehensionMemberOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x : {1,2}}\n" + "END";
		String expected = "---- MODULE test----\n"
				+ "k == {x \\in {1,2}: x \\in {1,2}} \n"
				+ "ASSUME k = {x \\in {1,2}: x \\in {1,2}} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehensionConjunctionEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x : {1,2} & 1 = 1}\n" + "END";
		String expected = "---- MODULE test----\n"
				+ "k == {x \\in {1,2}: x \\in {1,2} /\\ 1 = 1} \n"
				+ "ASSUME k = {x \\in {1,2}: x \\in {1,2} /\\ 1 = 1} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehensionEquals2Variables() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x,y | x : {1,2} & y = 1}\n" + "END";
		
		String expected = "---- MODULE test----\n"
				+ " k == {<<x, y>> \\in ({1, 2} \\times {1}): x \\in {1, 2} /\\ y = 1} \n"
				+ "ASSUME k = {<<x, y>> \\in ({1, 2} \\times {1}): x \\in {1, 2} /\\ y = 1} \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testExistQuantification2VariablesNotConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x,y.(x = 1 & x = y) \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in {1}, y \\in Int: x = 1 /\\ x = y \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension2VariablesConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & #x,y.(x = 1 & y = k + 1)\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 /\\ \\E x \\in {1}, y \\in {k +1}: x = 1 /\\ y = k + 1\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testNestedQuantifications() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(#y.(x = 1 & y = x))\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME \\E x \\in Int: \\E y \\in {x}: x = 1 /\\ y = x\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testQuantification() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & !x.(x = k => 1 = 1)\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 /\\ \\A x \\in {k} : x = k => 1 = 1 \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & !x.(x = k => 1 = 1)\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 /\\ \\A x \\in {k} : x = k => 1 = 1 \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testSelectParams() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k\n"
				+ "PROPERTIES k = 1..4"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo(a) = SELECT a : k THEN x:= a END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "k == 1 .. 4\n"
				+ "ASSUME k = 1 .. 4 \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(a) == a \\in k /\\ x' = a\n"
				+ "Next == \\E a \\in k: foo(a) \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testExist2Restrictions() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x = 1 & x = 2)"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "ASSUME \\E x \\in {1} \\cap {2} : x = 1 /\\ x = 2\n"
				+ "====";
		compare(expected, machine);
	}
	
}
