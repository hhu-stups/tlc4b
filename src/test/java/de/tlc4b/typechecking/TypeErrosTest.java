package de.tlc4b.typechecking;

import org.junit.Test;



import de.be4.classicalb.core.parser.exceptions.BException;
import de.tlc4b.exceptions.TypeErrorException;

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
