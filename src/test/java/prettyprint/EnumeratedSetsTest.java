package prettyprint;

import static prettyprint.TestPrinter.compare;

import org.junit.Ignore;
import org.junit.Test;

public class EnumeratedSetsTest {
		@Ignore
		@Test
		public void testSetComprehensionEquals() throws Exception {
			//TODO prettyprint sets
			String machine = "MACHINE test\n"
					+ "SETS set = {a,b,c}; set2 = {d}\n"
					+ "END";
			TestPrinter p = new TestPrinter(machine);
			
			String expected = "---- MODULE test----\n" 
					+ "CONSTANTS k \n"
					+ "ASSUME k = {x \\in {1}: x = 1} \n"
					+ "======";
			System.out.println(p.result);
			compare(expected, p.result);
		}
}
