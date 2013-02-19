package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import b2tla.exceptions.TypeErrorException;

import de.be4.classicalb.core.parser.exceptions.BException;

public class FunctionTest {

	
	@Test
	public void testLambda() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k =  %x.(x : {1} | 1) \n"
				+ "END";
		TestTypechecker t =  new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
	}
	
	
	@Test
	public void testSetOperatorOnFunction() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k =  %x.(x : {1} | 1) \\/ %x.(x : {1} | 1)  \n"
				+ "END";
		TestTypechecker t =  new TestTypechecker(machine);
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k").toString());
	}
	
	@Test
	public void testSetOperatorOnFunction2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = k \\/ k & k(1) = 1 \n"
				+ "END";
		TestTypechecker t =  new TestTypechecker(machine);
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLambdaException() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES %x.(x : {1} | TRUE) =  %x.(x : {1} | 1) \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	
	@Test 
	public void testFunctionCall() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k(TRUE) =  1 \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(BOOL,INTEGER)", t.constants.get("k").toString());
	}
	
	@Test 
	public void testFunctionCall2Arguments() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k(TRUE,1) =  1 \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(BOOL*INTEGER,INTEGER)", t.constants.get("k").toString());
	}
	
	@Test 
	public void testFunctionCallPair() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k(TRUE|->1) =  1 \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(BOOL*INTEGER,INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testFunctionCallException() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = %x.(x : {1} | TRUE) & k(1,1) = 1 \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test 
	public void testFunctionCallSucc() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k,k2 \n"
				+ "PROPERTIES k =  succ(k2) \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test 
	public void testTotalFunction() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = INT --> INT \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(FUNC(INTEGER,INTEGER))", t.constants.get("k").toString());
	}
	
	@Test 
	public void testTotalFunction2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = INT --> INT & k2 : k &  k2 = k2 \\/ k2 \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(POW(INTEGER*INTEGER))", t.constants.get("k").toString());
	}
	
	@Test 
	public void testDomain() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k : INT --> INT & k2 = dom(k) \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test 
	public void testDomain2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = dom(%x.(x = 1| 1)) \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testDomainException() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = dom(%x.(x = 1| 1)) \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	
	@Test 
	public void testRange() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k, k2 \n"
				+ "PROPERTIES k : INT --> INT & k2 = ran(k) \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test 
	public void testRange2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = ran(%x.(x = 1| 1)) \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRangeException() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = ran(%x.(x = 1| 1)) \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	
	@Test 
	public void testPartialFunction() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k = INT +-> INT \n"
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(POW(INTEGER*INTEGER))", t.constants.get("k").toString());
	}
	
	
}
