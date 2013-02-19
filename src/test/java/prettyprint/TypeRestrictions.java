package prettyprint;

import static org.junit.Assert.assertEquals;
import static prettyprint.TestPrinter.compare;

import org.junit.Ignore;
import org.junit.Test;

public class TypeRestrictions {
	@Test
	public void testSetComprehensionEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x = 1}\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "k == {x \\in {1}: x  = 1} \n"
				+ "ASSUME k = {x \\in {1}: x = 1} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testSetComprehensionMemberOf() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x : {1,2}}\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "k == {x \\in {1,2}: x \\in {1,2}} \n"
				+ "ASSUME k = {x \\in {1,2}: x \\in {1,2}} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testSetComprehensionConjunctionEquals() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x | x : {1,2} & 1 = 1}\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "k == {x \\in {1,2}: x \\in {1,2} /\\ 1 = 1} \n"
				+ "ASSUME k = {x \\in {1,2}: x \\in {1,2} /\\ 1 = 1} \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Ignore
	@Test
	public void testSetComprehensionEquals2Variables() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = {x,y | x : {1,2} & y = 1}\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n"
				+ " k == {<<x, y>> \\in ({1, 2} \\times {1}): x \\in {1, 2} /\\ y = 1} \n"
				+ "ASSUME k = {<<x, y>> \\in ({1, 2} \\times {1}): x \\in {1, 2} /\\ y = 1} \n"
				+ "======";
		System.out.println(p.result);
		//TODO TLA2B: add Tuple
		compare(expected, p.result);
	}
	
	@Test
	public void testExistQuantification2VariablesNotConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x,y.(x = 1 & x = y) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test----\n" + "EXTENDS Integers\n"
				+ "ASSUME \\E x \\in {1}, y \\in Int: x = 1 /\\ x = y \n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testSetComprehension2VariablesConstant() throws Exception {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = 1 & #x,y.(x = 1 & y = k + 1)\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Naturals\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 /\\ \\E x \\in {1}, \\in {k + 1}: x = 1 /\\ y = k + 1}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
	@Test
	public void testNestedQuantifications() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES #x.(#y.(x = 1 & y = x))\n" + "END";
		TestPrinter p = new TestPrinter(machine);
		
		String expected = "---- MODULE test ----\n" + "EXTENDS Naturals\n"
				+ "k == 1 \n"
				+ "ASSUME k = 1 /\\ \\E x \\in {1}, \\in {k + 1}: x = 1 /\\ y = k + 1}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
	}
	
}
