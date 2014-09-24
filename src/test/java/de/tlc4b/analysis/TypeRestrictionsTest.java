package de.tlc4b.analysis;

import static de.tlc4b.util.TestUtil.compare;

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
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testExistentielQuantification() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x = 1 & 1 = 1)\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in {1}: 1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testExistentielQuantification2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x = 1)\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in {1}: TRUE \n"
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
				+ "======";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testExistQuantification2VariablesNotConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x,y.(x = 1 & x = y) \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in {1}, y \\in Int: x = y \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testSubsetEq() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x <: {1,2,3} & 1 = 1) \n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in SUBSET({1, 2, 3}): 1 = 1 \n"
				+ "======";
		compare(expected, machine);
	}
	
	@Test
	public void testExist2VariablesConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & #x,y.(x = 1 & y = k + 1)\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME \\E x \\in {1}, y \\in {k +1}: TRUE \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testNestedQuantifications() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(#y.(x = 1 & y = x))\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME \\E x \\in {1} : (\\E y \\in {x} : TRUE) \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testQuantificationsInSetComprehension() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} = {x| #y.(x = 1 & y = x) & 1=1}\n" + "END";
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Integers\n"
				+ "k == 1 \n"
				+ "ASSUME {1} = {x \\in ({1}): (\\E y \\in {x} : TRUE) /\\ 1 = 1}\n"
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
				+ "ASSUME \\A x \\in {k} : 1 = 1 \n"
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
				+ "ASSUME \\A x \\in {k} : 1 = 1 \n"
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
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(a) == x' = a\n"
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
				+ "ASSUME \\E x \\in {1} \\cap {2} : TRUE\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testExistDependingVariables() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x,y.(x = 1 & y = x)"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Integers \n"
				+ "ASSUME \\E x \\in {1}, y \\in Int : y = x \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testExist3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(x = 1 & x = x)"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "ASSUME \\E x \\in {1} : x = x \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testPreParams() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo(a) = PRE a = 1 & a = a  THEN x:= 3 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(a) == (a = a)	/\\ x' = 3\n"
				+ "Next == \\E a \\in {1} : foo(a) \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testCoupleOfParameters() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #a,b.( (a,b) : {(1,1)})\n" + "END";
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E <<a,b>> \\in {<<1,1>>} : TRUE \n"
				+ "======";
		compare(expected, machine);
	}
	
	
}
