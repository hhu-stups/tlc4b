package prettyprint;

import static org.junit.Assert.assertEquals;
import static prettyprint.TestPrinter.compare;

import org.junit.Test;

public class RelationTest {

	@Test
	public void testCouple() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2) = (1|->2) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test----\n"
				+ "ASSUME <<1,2>> = <<1,2>>\n"
				+ "======";
		System.out.println(p.result);
		compare(expected, p.result);
	}
	
	@Test
	public void testCouple3() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2,3) = ((1,2),3) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "ASSUME <<<<1, 2>>, 3>> = <<<<1, 2>>, 3>>\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testCouple4() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES (1,2,3,4) = (((1,2),3),4) \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "ASSUME <<<<<<1, 2>>, 3>>, 4>> = <<<<<<1, 2>>, 3>>, 4>>\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testRelation() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <-> {2} = {{}, {(1,2)}} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME relation({1}, {2}) = {{}, {<<1, 2>>}}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testDomain() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES dom({(1,2)}) = {1} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME dom({<<1, 2>>}) = {1}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testDomain2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES dom({(1,2,3)}) = {(1,2)} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME dom({<<<<1, 2>>, 3>>}) = {<<1, 2>>}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testRange() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES ran({(1,2)}) = {2} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME RANGE({<<1, 2>>}) = {2}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testRange2() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES ran({(1,2,3)}) = {3} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME RANGE({<<<<1, 2>>, 3>>}) = {3}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testIdentity() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES id({1,2}) = {(1,1),(2,2)} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME id({1, 2}) = {<<1, 1>>, <<2, 2>>}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	
	@Test
	public void testDomainRestriction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <| {(1,2),(3,4)} = {(1,2)} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME domain_restriction({1}, {<<1, 2>>, <<3, 4>>}) = {<<1, 2>>}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	@Test
	public void testDomainSubstraction() throws Exception {
		String machine = "MACHINE test\n"
				+ "PROPERTIES {1} <<| {(1,2), (3,4)} = {(3,4)} \n" + "END";
		TestPrinter p = new TestPrinter(machine);
		String expected = "---- MODULE test ----\n"
				+ "EXTENDS Relations\n"
				+ "ASSUME domain_substraction({1}, {<<1, 2>>, <<3, 4>>}) = {<<3, 4>>}\n"
				+ "====";
		System.out.println(p.result);
		//compare(expected, p.result);
		assertEquals(expected, p.result);
	}
	
	//TODO range restriction and so on
	
}
