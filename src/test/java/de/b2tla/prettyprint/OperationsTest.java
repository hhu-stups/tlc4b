package de.b2tla.prettyprint;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Test;

public class OperationsTest {

	@Test
	public void testBecomesEqual() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1 \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Inv == x = 1\n"
				+ "Init == x = 1 \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testBecomesEqual2() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1 \n"
				+ "OPERATIONS\n"
				+ "foo = x:= 2 \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Inv == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == x' = 2\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}
	
	
	@Test
	public void testBlockSubstitution() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION BEGIN x := 1 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testBecomesSuchThat() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" 
				+ "INITIALISATION  x,y:(x = 1 & y = 1)\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Invariant == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x, y>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testBecomesSuchThatInOperations() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" 
				+ "INITIALISATION  x,y:(x = 1 & y = 1)\n"
				+ "OPERATIONS\n"
				+ " foo = x,y:(x = 1 & y = 1)\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Invariant == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "foo == x' = 1 /\\ y' = 1\n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testBecomesSuchPreviousValue() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" 
				+ "INITIALISATION  x,y:(x = 1 & y = 1)\n"
				+ "OPERATIONS\n"
				+ " foo = x:(x = x$0 + 1)\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x, y \n"
				+ "Invariant == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "foo == x' = x + 1 /\\ UNCHANGED <<y>>\n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testOperationParameter() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION BEGIN x := 1 END\n"
				+ "OPERATIONS\n"
				+ "foo(p) = PRE p = 1 THEN x:= p END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(p) == p = 1 /\\ x' = p\n"
				+ "Next == \\E p \\in {1} : foo(p)\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testAny() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION BEGIN x := 1 END\n"
				+ "OPERATIONS\n"
				+ "foo = ANY p WHERE p = 1 THEN x := p END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == \\E p \\in {1} : p = 1 /\\ x' = p\n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testOpParamterAny() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION BEGIN x := 1 END\n"
				+ "OPERATIONS\n"
				+ "foo(p) = ANY p2 WHERE p = 1 & p2 = 1THEN x:= p+p2 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(p) == \\E p2 \\in {1} : p = 1 /\\ p2 = 1 /\\ x' = p + p2\n"
				+ "Next == \\E p \\in {1} : foo(p)\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testSkip() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo = skip\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == UNCHANGED <<x>>\n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testSkip2() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo = PRE 1 = 1 THEN skip END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == 1 = 1 /\\ UNCHANGED <<x>>\n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	
	@Test
	public void testSelect() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo = SELECT x = 1 THEN x:= x + 1 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == x = 1 /\\ x' = x + 1\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}

	@Test
	public void testSelectParams() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo(a) = SELECT a = 1 THEN x:= a END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo(a) == a = 1 /\\ x' = a\n"
				+ "Next == \\E a \\in {1}: foo(a) \n"
				+ "====";
		compare(expected, machine);
	}

	@Test
	public void testBecomesElement() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x :: {1}\n"
				+ "OPERATIONS\n"
				+ "foo = x :: {2} \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x \\in {1} \n"
				+ "foo == x' \\in {2} \n"
				+ "Next == foo\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testIfThen() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo = IF 1 = 1 THEN x := 1 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == (IF 1 = 1 THEN x' = 1 ELSE  UNCHANGED <<x>>)\n"
				+ "Next ==  foo \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testSelectWhen() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "foo = SELECT x = 1 THEN x:= 1 WHEN x = 2 THEN x := 2 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == (( ((x = 1) /\\ (x' = 1)) \\/ (x = 2 /\\ x' = 2)))\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}
	
	
	@Test
	public void testSelectWhen2() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" 
				+ "INITIALISATION x,y := 1,1\n"
				+ "OPERATIONS\n"
				+ "foo = SELECT x = 1 THEN x:= 1 WHEN x = 2 THEN skip END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x,y \n"
				+ "Invariant == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  (( ((x = 1) /\\ (x' = 1)) \\/ (x = 2 /\\ UNCHANGED <<x>>)) /\\ UNCHANGED <<y>>)\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testSelectWhen3() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" 
				+ "INITIALISATION x,y := 1,1\n"
				+ "OPERATIONS\n"
				+ "foo = PRE x= 1 THEN SELECT x = 1 THEN x:= 1 WHEN x = 2 THEN skip END || y:= 1 END\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Invariant == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo == x = 1 /\\ (( ((x = 1) /\\ (x' = 1))\n"
				+ "\\/ (x = 2 /\\  UNCHANGED <<x>>))) /\\ y' = 1\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testOutputParams() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS\n"
				+ "res <-- foo = res:= x\n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x \n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1 \n"
				+ "foo == TRUE /\\ UNCHANGED <<x>>\n"
				+ "Next == foo \n"
				+ "====";
		compare(expected, machine);
	}
	
}
