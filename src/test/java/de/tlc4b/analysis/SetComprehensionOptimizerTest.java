package de.tlc4b.analysis;

import de.tlc4b.util.TestUtil;

import org.junit.Ignore;
import org.junit.Test;

public class SetComprehensionOptimizerTest {

	@Test
	public void testSetComprehension1() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y | x : 1..10 & y = x + 1} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {<<x, x + 1>>: x \\in {x \\in ((1 .. 10)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	/**
	 * The type restrictor will simplify the expression.
	 * @throws Exception
	 */
	@Test
	public void testNotOptimized() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y | x = 1 & y = 2} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "ASSUME {<<x, y>> \\in (({1}) \\times ({2})): TRUE} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y|  x : 1..10 & x = y & y = x} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {<<y, y>>: y \\in {y \\in ((1 .. 10)): y = y}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension4() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y,c| c : {TRUE} & x : 1..2 & x = y+1 & y = x-1} /= {} \n" 
				+ "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Integers\n"
				+ "ASSUME {<<<<y + 1, y>>, c>>: <<y, c>> \\in {<<y, c>> \\in ((Int) \\times ({TRUE})): y + 1 \\in (1 .. 2) /\\ y = (y + 1) - 1}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension5() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y| x : 1..2 & y : 1..100 & x = y} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {<<y, y>>: y \\in {y \\in ((1 .. 2) \\cap (1 .. 100)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testSetComprehension6() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {a,b,c,d| a = b & b : {1} & c : {1} & d : {1}} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Integers\n"
				+ "ASSUME {<<<<<<t_[1], t_[2]>>, t_[3]>>, t_[4]>>: t_ \\in {<<a, b, c, d>> \\in (Int) \\times ({1}) \\times ({1}) \\times ({1}): a = b}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	
	@Test
	public void testDomain() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES dom({x,y|  x : 1..10 & x = y}) /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {y: y \\in {y \\in ((1 .. 10)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testDomain2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {a,b| a : 1..3 & b = dom({x,y|  y : 1..10 & x = y+1}) } /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {<<a, {y + 1: y \\in {y \\in ((1 .. 10)): TRUE}}>>: a \\in {a \\in ((1 .. 3)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Ignore
	@Test
	public void testDomain3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {a,b| a = 1 & b = dom({a,b|  a : 1..10 & a = b+1}) } /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {<<a, {y + 1: y \\in {y \\in ((1 .. 10)): TRUE}}>>: a \\in {a \\in ((1 .. 3)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	
	@Test
	public void testDoubleDomain() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES dom(dom({a,b,c|  a = 1 & b = 1 & c : 1..10 })) /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Naturals\n"
				+ "ASSUME {1: c \\in {c \\in ((1 .. 10)): TRUE}} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
	@Test
	public void testSelfDependency() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {x,y|  y : 1..10 & x = x + 1 -1} /= {} \n" + "END";
		String expected = "---- MODULE test----\n" 
				+ "EXTENDS Integers\n"
				+ "ASSUME {<<x, y>> \\in ((Int) \\times ((1 .. 10))): x = (x + 1) - 1} # {} \n"
				+ "======";
		TestUtil.compare(expected, machine);
	}
	
}
