package prettyprint;

import java.io.IOException;

import org.junit.Test;

import tlc2.tool.WorkerException;

public class SimpleExamples {

	
	@Test
	public void testSimple1() throws Exception {
		String machine = "MACHINE test\n" 
				+ "VARIABLES x,y\n"
							+ "INVARIANT x = 1 & y = 1\n"
							+ "INITIALISATION x,y := 1,1 \n"
							+ "OPERATIONS foo = x := 1\n" 
							+ "END";
		TestPrinter p = new TestPrinter(machine);
		
		
		String expected = "---- MODULE test ----\n"
				+ "VARIABLES x, y\n"
				+ "Inv == x = 1 /\\ y = 1\n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "foo == x' = 1 /\\ UNCHANGED <<y>> \n"
				+ "bar ==  IF x = 1 THEN x' = 2 /\\ UNCHANGED <<y>> ELSE y' = 2 /\\ UNCHANGED <<x>> \n"
				+ "Next == bar \\/ foo \n"
				+ "====";
		
		System.out.println(p.result);
		System.out.println(p.config);
		
		Tester tester = new Tester(p.result, p.config);
		//compare(expected, p.result);
	}
}
