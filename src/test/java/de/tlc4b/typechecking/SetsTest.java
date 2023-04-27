package de.tlc4b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;



import de.be4.classicalb.core.parser.exceptions.BException;
import de.tlc4b.exceptions.TypeErrorException;

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
	
	@Test
	public void testEventBSetComprehension() throws BException {
		String machine = "MACHINE test\n" 
				+ "CONSTANTS k,k2,k3 \n"
				+ "PROPERTIES k = {x,y| x = k2(k3) & y : {TRUE}} & k2(2)=1\n" 
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("FUNC(INTEGER,INTEGER)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	@Test
	public void testEventBSetComprehension2() throws BException {
		String machine = "MACHINE test\n" 
				+ "CONSTANTS k,k2 \n"
				+ "PROPERTIES k = {a,b| a : k2 & b = a'foo} & k2={rec(foo:\"123\",bar:TRUE)}\n" 
				+ "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(struct(foo:STRING,bar:BOOL)*STRING)", t.constants.get("k").toString());
		assertEquals("POW(struct(foo:STRING,bar:BOOL))", t.constants.get("k2").toString());
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
	
	@Test
	public void testUnion() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = {1} \\/ k2 \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnionException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k, k2 \n"
				+ "PROPERTIES k = {1} \\/ 1 \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnionException2() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k, k2 \n"
				+ "PROPERTIES 1 = {1} \\/ k \n" + "END";
		new TestTypechecker(machine);
	}
	
	@Test
	public void testCard() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = card({1}) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
	@Test
	public void testGerneralUnion() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = union({{1}, {2}}) \n" + "END";
		TestTypechecker t = new TestTypechecker(machine);
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testGerneralUnionException() throws BException {
		String machine = "MACHINE test\n" + "CONSTANTS k \n"
				+ "PROPERTIES k = union({1}) \n" + "END";
		new TestTypechecker(machine);
	}
	
}
