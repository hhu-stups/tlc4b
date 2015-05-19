package de.tlc4b.ltl;


import static de.tlc4b.util.TestUtil.compareEqualsConfig;
import static de.tlc4b.util.TestUtil.compareLTLFormula;

import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import de.tlc4b.TLC4BGlobals;
import de.tlc4b.exceptions.LTLParseException;
import de.tlc4b.exceptions.ScopeException;
import de.tlc4b.exceptions.TypeErrorException;


public class LtlFormulaTest {

	@BeforeClass
	public static void setUp(){
		TLC4BGlobals.setTestingMode(true);
	}
	
	@Test (expected = ScopeException.class)
	public void testScopeException() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS foo = x := 1"
				+ "END";
		compareLTLFormula("", machine, "G{y = 1}");
	}
	
	@Test (expected = TypeErrorException.class)
	public void testTypeError() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS foo = x := 1"
				+ "END";
		compareLTLFormula("", machine, "G{x = FALSE}");
	}
	
	@Test (expected = ScopeException.class) 
	public void testUnkownOperation() throws Exception {
		String machine = "MACHINE test\n"
				+ "END";
		compareLTLFormula("", machine, "e(foo)");
	}
	
	@Test 
	public void testGobally() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("[](1 = 1)", machine, "G{1 = 1}");
	}
	
	@Test 
	public void testFinally() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("<>(1=1)", machine, "F{1 = 1}");
	}
	
	@Test 
	public void testEnabled() throws Exception {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo = skip \n"
				+ "END";
		compareLTLFormula("ENABLED(foo)", machine, "e(foo)");
	}
	
	@Test  (expected = ScopeException.class)
	public void testEnabledUnknownOperation() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("ENABLED(foo)", machine, "e(foo)");
	}
	
	
	
	@Test 
	public void testTrue() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("TRUE", machine, "true");
	}
	
	@Test 
	public void testFalse() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("FALSE", machine, "false");
	}
	
	@Test 
	public void testImplication() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("FALSE => TRUE", machine, "false => true");
	}
	
	@Test 
	public void testAnd() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("TRUE /\\ FALSE", machine, "true & false");
	}
	
	@Test 
	public void testOr() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("TRUE \\/ FALSE", machine, "true or false");
	}
	
	@Test 
	public void testNegation() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("\\neg(TRUE)", machine, "not(true)");
	}
	
	@Test (expected = ScopeException.class)
	public void testUntil() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "true U false");
	}
	
	@Test (expected = ScopeException.class)
	public void testWeakUntil() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "true W false");
	}
	
	@Test (expected = ScopeException.class)
	public void testRelease() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "true R false");
	}
	
	@Test (expected = ScopeException.class)
	public void testHistory() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "H false");
	}
	
	@Test (expected = ScopeException.class)
	public void testOnce() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "O false");
	}
	
	@Test (expected = ScopeException.class)
	public void testYesterday() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "Y false");
	}
	
	@Test (expected = ScopeException.class)
	public void testSince() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "true S false");
	}
	
	@Test (expected = ScopeException.class)
	public void testTrigger() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "true T false");
	}
	
	@Test (expected = ScopeException.class)
	public void testAction() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("", machine, "[foo]");
	}
	
	
	@Test (expected = LTLParseException.class)
	public void testWeakFairnessParseError() throws Exception {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo = skip\n"
				+ "END";
		compareLTLFormula("", machine, "WF(foo)");
	}
	
	@Test
	public void testDeterministic() throws Exception {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo = skip; bar = skip; bazz = skip\n"
				+ "END";
	    String expected = "\\neg(ENABLED(foo) /\\ ENABLED(bar)) /\\ \\neg(ENABLED(foo)  /\\ ENABLED(bazz)) /\\ \\neg(ENABLED(bar) /\\ ENABLED(bazz))";
		compareLTLFormula(expected, machine, "deterministic(foo,bar,bazz)");
	}
	
	@Test
	public void testDeadlock() throws Exception {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo = skip; bar = skip; bazz = skip\n"
				+ "END";
	    String expected = "\\neg(ENABLED(foo) \\/ ENABLED(bar) \\/ ENABLED(bazz))";
		compareLTLFormula(expected, machine, "deadlock");
	}
	
	@Test
	public void testDeadlockOperationParameter() throws Exception {
		String machine = "MACHINE test\n"
				+ "OPERATIONS foo(a) = SELECT a : 1..3 THEN skip END\n"
				+ "END";
	    String expected = "\\neg(ENABLED(\\E a \\in (1 .. 3) : foo(a)))";
		compareLTLFormula(expected, machine, "deadlock");
	}
	
	@Test
	public void testWeakFairness() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS foo = skip\n"
				+ "END";
		String expected = "([]<><<foo>>_vars\\/[]<>~ENABLED(foo)\\/[]<>ENABLED(foo/\\x'=x))=>TRUE";
		compareLTLFormula(expected, machine, "WF(foo) => true");
	}
	
	@Test 
	public void testStrongFairness() throws Exception {
		String machine = "MACHINE test\n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS foo = x := 1"
				+ "END";
		String expected = "([]<><<foo>>_vars\\/<>[]~ENABLED(foo)\\/[]<>ENABLED(foo/\\x'=x))=>TRUE";
		compareLTLFormula(expected, machine, "SF(foo) => true");
	}
	
	@Test 
	public void testExistentialQuantification() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula(" \\E p \\in {1}: p = 1", machine, "#p.({p=1} & {p = 1})");
	}
	
	@Test 
	public void testExistentialQuantification2() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("\\E p \\in {1}: 1 = 1 /\\ p = 1", machine, "#p.({p=1 & 1 = 1} & {p = 1})");
	}
	
	@Test 
	public void testForallQuantification() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("\\A p \\in {1}: p = 1", machine, "!p.({p=1} => {p = 1})");
	}
	
	@Test 
	public void testForallQuantification2() throws Exception {
		String machine = "MACHINE test END";
		compareLTLFormula("\\A p \\in {1}: 1 = 1 => p = 1", machine, "!p.({p=1 & 1=1 } => {p = 1})");
	}
	
	@Ignore
	@Test 
	public void testLTLFormulaInDefinitions() throws Exception {
		final String machine = "MACHINE test\n"
				+ "DEFINITIONS ASSERT_LTL == \"false\" \n"
				+ "VARIABLES x\n"
				+ "INVARIANT x = 1\n"
				+ "INITIALISATION x := 1\n"
				+ "OPERATIONS foo = x := 1"
				+ "END";
		
		final String expected = "---- MODULE test ----\n"
				+ "VARIABLES x\n"
				+ "Invariant == x = 1\n"
				+ "Init == x = 1\n"
				+ "foo == x' = 1\n\n"
				+ "Next == \\/ foo\n"
				+ "Spec == Init /\\ [][Next]_<<x>> /\\ WF_<<x>>(Next)\n"
				+ "ASSERT_LTL == FALSE\n"
				+ "====";
		final String config = "SPECIFICATION Spec\nINVARIANT Invariant\nPROPERTIES ASSERT_LTL\n";
		
		compareEqualsConfig(expected, config, machine);
	}
	
}
