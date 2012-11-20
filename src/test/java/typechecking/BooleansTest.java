package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;
import exceptions.TypeErrorException;

public class BooleansTest {
	
	@Test
	public void testTrue() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = TRUE \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("BOOL", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testTrueException() throws BException {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 = TRUE \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testFalse() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = FALSE \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("BOOL", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testFalseException() throws BException {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 = FALSE \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testBool() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = BOOL \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testBoolException() throws BException {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 = BOOL \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testConvertPredicate() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = bool(1=1) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("BOOL", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testConvertPredicateException() throws BException {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 = bool(1=1) \n" + "END";
		new TestTypechecker(machine);
	}
	
	
}
