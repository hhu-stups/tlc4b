package prettyprint;

import static prettyprint.TestPrinter.compare;

import org.junit.Test;

public class UnchangedVariables {

	@Test
	public void testIfThenElse() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n" + "INITIALISATION x,y := 1,1 \n"
				+ "OPERATIONS foo = IF x = 1 THEN x:= 2 ELSE y := 2 END \n"
				+ "END";
		TestPrinter p = new TestPrinter(machine);

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  IF x = 1 THEN x' = 2 /\\ UNCHANGED <<y>> ELSE y' = 2 /\\ UNCHANGED <<x>>\n"
				+ "Next == foo\n" + "====";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testChoice() throws Exception {
		String machine = "MACHINE test\n" + "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1\n"
				+ "INITIALISATION x,y := 1,1 \n"
				+ "OPERATIONS foo = CHOICE x := 1 OR y:= 2 END\n" 
				+ "END";
		TestPrinter p = new TestPrinter(machine);

		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y \n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1\n"
				+ "foo ==  (x' = 1 /\\ UNCHANGED <<y>>) \\/ (y' = 2 /\\ UNCHANGED <<x>>)\n"
				+ "Next == foo\n" + "====";
		System.out.println(p.result);
		compare(expected, p.result);
	}
}
