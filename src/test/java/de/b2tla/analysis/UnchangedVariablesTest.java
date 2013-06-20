package de.b2tla.analysis;

import static de.b2tla.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

import de.b2tla.exceptions.SubstitutionException;

public class UnchangedVariablesTest {

	@Test
	public void testIfThen() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES a,b,c\n"
				+ "INVARIANT a = 1 & b = 1 & c = 1\n" 
				+ "INITIALISATION a,b,c := 1,1,1 \n"
				+ "OPERATIONS foo = IF 1 = 1 THEN a := 2 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES a, b,c \n"
				+ "Inv == a = 1 /\\ b = 1 /\\ c = 1\n"
				+ "Init == a = 1 /\\ b = 1 /\\ c = 1\n"
				+ "foo ==  (IF 1 = 1 THEN a' = 2 ELSE UNCHANGED <<a>>) /\\ UNCHANGED <<b,c>>\n"
				+ "Next == foo\n" + "====";
		compare(expected, machine);
	}
	

	@Test (expected = SubstitutionException.class)
	public void testParallelSubstitution() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES a,b,c\n"
				+ "INVARIANT a = 1 & b = 1 & c = 1\n" 
				+ "INITIALISATION a,b,c := 1,1,1 \n"
				+ "OPERATIONS foo = a := 2 || a := 3 \n"
				+ "END";
		compare(null, machine);
	}
	
	
	@Ignore
	@Test
	public void testFunction() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x\n"
				+ "INVARIANT x = %p.(p: {1}| 1)\n" 
				+ "INITIALISATION x := %p.(p: {1}| 1) \n"
				+ "OPERATIONS foo = x(1):= 2 \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  IF x = 1 THEN x' = 2 /\\ UNCHANGED <<y>> ELSE y' = 2 /\\ UNCHANGED <<x>>\n"
				+ "Next == foo\n" + "====";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testIfThenElse() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" + "INITIALISATION x,y := 1,1 \n"
				+ "OPERATIONS foo = IF x = 1 THEN x:= 2 ELSE y := 2 END \n"
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  IF x = 1 THEN x' = 2 /\\ UNCHANGED <<y>> ELSE y' = 2 /\\ UNCHANGED <<x>>\n"
				+ "Next == foo\n" + "====";
		compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testChoice() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n"
				+ "INITIALISATION x,y := 1,1 \n"
				+ "OPERATIONS foo = CHOICE x := 1 OR y:= 2 END\n" 
				+ "END";

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  (x' = 1 /\\ UNCHANGED <<y>>) \\/ (y' = 2 /\\ UNCHANGED <<x>>)\n"
				+ "Next == foo\n" + "====";
		compare(expected, machine);
	}
}
