package typechecking;

import org.junit.Test;

import b2tla.exceptions.TypeErrorException;

import de.be4.classicalb.core.parser.exceptions.BException;

public class TypeErrosTest {
	
	@Test (expected = TypeErrorException.class)
	public void test1() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES k : k \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void test2() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES {k} : {k} \n"
				+ "END";
		new TestTypechecker(machine);
	}
	
	@Test (expected = TypeErrorException.class)
	public void test3() throws BException {
		String machine = "MACHINE test\n"
				+ "CONSTANTS k \n"
				+ "PROPERTIES {k} : {{k}} \n"
				+ "END";
		new TestTypechecker(machine);
	}
}
