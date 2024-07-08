package de.tlc4b.prettyprint;

import static de.tlc4b.util.TestUtil.compare;

import org.junit.Test;

import de.tlc4b.exceptions.SubstitutionException;

public class SubstitutionsTest {
	
	
	@Test (expected = SubstitutionException.class)
	public void testVariableAssignedTwice() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x\n"
				+ "INVARIANT x = 1 \n" + "INITIALISATION x := 1 || x := 1 \n"
				+ "END";
		compare(null, machine);
	}
	
	@Test (expected = SubstitutionException.class)
	public void testMissingVariableAssignment() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y \n"
				+ "INVARIANT x = 1 & y = 1 \n" + "INITIALISATION x := 1 \n"
				+ "END";
		compare(null, machine);
	}

	@Test
	public void testAssignSequentialSubstitutionSimple() throws Exception {
		String machine = "MACHINE test\n"
			+ "VARIABLES x,y\n"
			+ "INVARIANT x = 1 & y = 3 \n"
			+ "INITIALISATION x := 1 ; y := x \n"
			+ "OPERATIONS\n"
			+ " op1 = BEGIN x := 1 ; y := x + 1 END; \n"
			+ " op2 = BEGIN x := 1 || y := x + 1 END; \n"
			+ " op3 = BEGIN x := y ; y := 1 END; \n"
			+ " op4 = BEGIN x := y || y := 1 END; \n"
			+ " op5 = BEGIN x, y := x + 1, x + 1 END \n"
			+ "END";

		String expected = "---- MODULE test ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Invariant1 == x = 1\n"
			+ "Invariant2 == y = 3\n"
			+ "Init == x = 1 /\\ y = x\n"
			+ "\n"
			+ "op1 == x' = 1 /\\ y' = x' + 1\n"
			+ "\n"
			+ "op2 == x' = 1 /\\ y' = x + 1\n"
			+ "\n"
			+ "op3 == x' = y /\\ y' = 1\n"
			+ "\n"
			+ "op4 == x' = y /\\ y' = 1\n"
			+ "\n"
			+ "op5 == x' = x + 1 /\\ y' = x + 1\n"
			+ "\n"
			+ "Next == \\/ op1\n"
			+ "\t\\/ op2\n"
			+ "\t\\/ op3\n"
			+ "\t\\/ op4\n"
			+ "\t\\/ op5\n"
			+ "====";
		compare(expected, machine);
	}

	@Test
	public void testAssignSequentialSubstitutionNested() throws Exception {
		String machine = "MACHINE test\n"
			+ "VARIABLES x,y,z\n"
			+ "INVARIANT x = 1 & y = 3 & z = 0\n"
			+ "INITIALISATION x := 1 ; y := x || z := x \n"
			+ "OPERATIONS\n"
			+ " op1 = BEGIN y := x ; z := 5 || x := y * z END; \n"
			+ " op2 = BEGIN y := x || z := y ; x := x + y + z ; ANY q WHERE q : INT & x = 5 & y = 6 THEN skip END END; \n"
			+ " op3 = BEGIN y := x || z := y ; x := x + y + z || ANY q WHERE q : INT & x = 5 & y = 6 THEN skip END END; \n"
			+ " op4 = BEGIN y := x || z := y || x := x + y + z || ANY q WHERE q : INT & x = 5 & y = 6 THEN skip END END; \n"
			+ " op5 = BEGIN BEGIN y := x END ; BEGIN x := y END ; SELECT x = 5 & z = 6 THEN z := x + y END END \n"
			+ "END";

		String expected = "---- MODULE test ----\n"
			+ "EXTENDS Integers\n"
			+ "VARIABLES x, y, z\n"
			+ "Invariant1 == x = 1\n"
			+ "Invariant2 == y = 3\n"
			+ "Invariant3 == z = 0\n"
			+ "Init == x = 1 /\\ y = x /\\ z = x\n"
			+ "\n"
			+ "op1 == y' = x /\\ z' = 5 /\\ x' = y' * z\n"
			+ "\n"
			+ "op2 == y' = x /\\ z' = y /\\ x' = x + y' + z' /\\ \\E q \\in (-1..3) : x' = 5 /\\ y' = 6 /\\ TRUE\n"
			+ "\n"
			+ "op3 == y' = x /\\ z' = y /\\ x' = x + y' + z' /\\ \\E q \\in (-1..3) : x = 5 /\\ y' = 6 /\\ TRUE\n"
			+ "\n"
			+ "op4 == y' = x /\\ z' = y /\\ x' = x + y + z /\\ \\E q \\in (-1..3) : x = 5 /\\ y = 6 /\\ TRUE\n"
			+ "\n"
			+ "op5 == y' = x /\\ x' = y' /\\ (((x' = 5 /\\ z = 6) /\\ z' = x' + y'))\n"
			+ "\n"
			+ "Next == \\/ op1\n"
			+ "\t\\/ op2\n"
			+ "\t\\/ op3\n"
			+ "\t\\/ op4\n"
			+ "\t\\/ op5\n"
			+ "====";
		compare(expected, machine);
	}

	@Test
	public void testBecomesElementOfSequentialSubstitution() throws Exception {
		String machine = "MACHINE test\n"
			+ "VARIABLES x,y\n"
			+ "INVARIANT x = 1 & y = 3 \n"
			+ "INITIALISATION x := 1 ; y := x \n"
			+ "OPERATIONS\n"
			+ " op1 = PRE x < 6 THEN x :: 4..6 ; y := x + 1 END; \n"
			+ " op2 = PRE x < 6 THEN x :: 4..6 || y := x + 1 END; \n"
			+ " op3 = PRE x < 6 THEN x := 1 ; y :: {x} END; \n"
			+ " op4 = PRE x < 6 THEN x := 1 || y :: {x} END \n"
			+ "END";

		String expected = "---- MODULE test ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Invariant1 == x = 1\n"
			+ "Invariant2 == y = 3\n"
			+ "Init == x = 1 /\\ y = x\n"
			+ "\n"
			+ "op1 == x < 6\n"
			+ "\t/\\ (x' \\in (4 .. 6) /\\ y' = x' + 1)\n"
			+ "\n"
			+ "op2 == x < 6\n"
			+ "\t/\\ (x' \\in (4 .. 6) /\\ y' = x + 1)\n"
			+ "\n"
			+ "op3 == x < 6\n"
			+ "\t/\\ (x' = 1 /\\ y' \\in {x'})\n"
			+ "\n"
			+ "op4 == x < 6\n"
			+ "\t/\\ (x' = 1 /\\ y' \\in {x})\n"
			+ "\n"
			+ "Next == \\/ op1\n"
			+ "\t\\/ op2\n"
			+ "\t\\/ op3\n"
			+ "\t\\/ op4\n"
			+ "====";
		compare(expected, machine);
	}

	@Test
	public void testBecomesSuchSequentialSubstitution() throws Exception {
		String machine = "MACHINE test\n"
			+ "VARIABLES x,y\n"
			+ "INVARIANT x = 1 & y = 3 \n"
			+ "INITIALISATION x := 1 ; y := x \n"
			+ "OPERATIONS\n"
			+ " op1 = BEGIN x : (x : 4..6) ; y := x END; \n"
			+ " op2 = BEGIN x : (x : 4..6) || y := x END; \n"
			+ " op3 = BEGIN x := 1 ; y : (x = y) END; \n"
			+ " op4 = BEGIN x := 1 || y : (x = y) END \n"
			+ "END";

		String expected = "---- MODULE test ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Invariant1 == x = 1\n"
			+ "Invariant2 == y = 3\n"
			+ "Init == x = 1 /\\ y = x\n"
			+ "\n"
			+ "op1 == x' \\in (4 .. 6) /\\ y' = x'\n"
			+ "\n"
			+ "op2 == x' \\in (4 .. 6) /\\ y' = x\n"
			+ "\n"
			+ "op3 == x' = 1 /\\ y' \\in {x'}\n"
			+ "\n"
			+ "op4 == x' = 1 /\\ y' \\in {x}\n"
			+ "\n"
			+ "Next == \\/ op1\n"
			+ "\t\\/ op2\n"
			+ "\t\\/ op3\n"
			+ "\t\\/ op4\n"
			+ "====";
		compare(expected, machine);
	}

	@Test (expected = SubstitutionException.class)
	public void testSimpleSequentialSubstitutionAssignedTwice() throws Exception {
		String machine = "MACHINE test\n"
			+ "VARIABLES x,y\n"
			+ "INVARIANT x = 1 & y = 3 \n"
			+ "INITIALISATION x := 1 ; y := x ; x := y \n"
			+ "END";
		compare(null, machine);
	}
	
	@Test
	public void testLet() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION LET a,b BE a = 1 & b = 2 IN x := a +b END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == \\E a \\in {1}, b \\in {2} : TRUE /\\ x = a + b \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testAny() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION ANY a,b WHERE a = 1 & b = 2 THEN x := a +b END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == \\E a \\in {1}, b \\in {2} : x = a + b \n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testPre() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION PRE 1 = 1 THEN x := 1 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == 1 = 1 \n/\\ x = 1\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testAssert() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION ASSERT 1 = 1 THEN x := 1 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == 1 = 1 \n/\\ x = 1\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testNotDeterministicElementOf() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION x :: {1} \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == x \\in {1}\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
	@Test
	public void testIFElseIFSubstitution() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n" 
				+ "INITIALISATION IF 1=1 THEN x:= 1 ELSIF 1=2 THEN x:= 2 ELSE x:= 4 END \n"
				+ "END";
		
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Invariant1 == x = 1\n"
				+ "Init == (CASE 1 = 1 -> x = 1 [] 1 = 2 -> x = 2 [] OTHER -> x = 4)\n"
				+ "Next == 1 = 2 /\\ UNCHANGED <<x>>\n"
				+ "====";
		compare(expected, machine);
	}
	
}
