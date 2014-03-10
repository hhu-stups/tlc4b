package standard;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Hashtable;

import org.junit.Ignore;
import org.junit.Test;




import de.b2tla.analysis.Ast2String;
import de.b2tla.analysis.MachineContext;
import de.b2tla.analysis.Typechecker;
import de.b2tla.analysis.unchangedvariables.UnchangedVariablesFinder;
import de.b2tla.exceptions.SubstitutionException;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;

public class SubsitutionTest {

	@Test
	public void test() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y\n"
				+ "INVARIANT x = 1 & y = 1 \n" + "INITIALISATION x,y := 1,1 \n"
				+ "OPERATIONS foo = x := 1 \n" + "END";
	}

	@Ignore
	@Test (expected = SubstitutionException.class)
	public void testVariableAssignedTwice() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x\n"
				+ "INVARIANT x = 1 \n" + "INITIALISATION x := 1 || x := 1 \n"
				+ "END";
	}
	
	@Ignore
	@Test  (expected = SubstitutionException.class)
	public void testMissingVariableAssignment() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y \n"
				+ "INVARIANT x = 1 & y = 1 \n" + "INITIALISATION x := 1 \n"
				+ "END";
	}

	@Test
	public void test2() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,z \n"
				+ "OPERATIONS foo = x := 1 || y := 1 || z := 1\n" + "END";
	}
	
	@Test
	public void test3() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,1 \n"
				+ "OPERATIONS foo = CHOICE x := 1 OR y := 1 OR z := 1 END\n" + "END";
	}

	@Test
	public void test4() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,1 \n"
				+ "OPERATIONS "
				+ "foo = z := 1 || CHOICE x := 1 OR y := 1 END\n" 
				+ "END";
	}
	
	
	@Test
	public void test5() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,1 \n"
				+ "OPERATIONS "
				+ "foo = CHOICE x := 1 OR y := 1 END || z := 1 \n" 
				+ "END";
	}
	
	@Test
	public void testChoice() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,1 \n"
				+ "OPERATIONS "
				+ "foo = CHOICE x := 1 OR y := 1 END \n" 
				+ "END";
	}
	
	@Test
	public void testIF() throws BException {
		String machine = "MACHINE test\n" + "VARIABLES x,y,z\n"
				+ "INVARIANT x = 1 & y = 1 & z = 1 \n"
				+ "INITIALISATION x,y,z := 1,1,1 \n"
				+ "OPERATIONS "
				+ "foo = IF x = 1 THEN x := 2 ELSE y:= 2 END \n" 
				+ "END";
	}

	

}
