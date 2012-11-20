package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.be4.classicalb.core.parser.exceptions.BException;
import exceptions.TypeErrorException;

public class SetsTest {

	@Test
	public void testEmptySet() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {} = {} \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testEmptySetException() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = {} \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testSetExtension() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = {1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testSetExtensionException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES 1 = {1} \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testSetExtension2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = {k2,1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testSetExtensionException2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = {1,TRUE} \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testSetComprehension() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = {x| x = 1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test
	public void testSetComprehension2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = {x,y| x = 1 & y = TRUE} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testSetComprehensionException() throws BException {
		String machine = "MACHINE test\n"
				+ "PROPERTIES 1 = {x| x = 1} \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}
	
	@Test
	public void testPowerSet() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = POW({1}) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(POW(INTEGER))", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testPowerSetException() throws BException {
		String machine = "MACHINE test\n" 
				+ "PROPERTIES 1 = POW({1}) \n" + "END";
		new TestTypechecker(machine);
	}
	
}
