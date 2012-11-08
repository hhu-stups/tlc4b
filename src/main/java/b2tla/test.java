package b2tla;
import java.util.Hashtable;
import java.util.Map.Entry;

import btypes.BType;



import analysis.Ast2String;
import analysis.MachineDeclarationsCollector;
import analysis.ScopeChecker;
import analysis.transformation.DefinitionsEliminator;


import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;


public class test {

	/**
	 * @param args
	 * @throws BException 
	 */
	public static void main(String[] args) throws BException {

		String testMachine = "MACHINE Testing(a,B) \n"
				+ "CONSTRAINTS a = 1"
				+ "SETS S; E = {e1,e2} \n"
				+ "CONSTANTS c \n"
				+ "PROPERTIES c = 1 \n"
				+ "VARIABLES d \n"
				+ "INVARIANT a = B & c = d\n"
				+ "INITIALISATION d,d :=1 \n"
				+ "OPERATIONS \n"
				+ "foo = d:= 2 || bar ; \n"
				+ "bar = d(1) := 3"
				+ "END";
		
		
		
		/*		+ "INVARIANT 1 = 1 \n" 
				+ "INITIALISATION a  := 1 || b := 1 \n"
				+ "OPERATIONS \n"
				+ "foo = a:= 2 || b:= 4 ; \n"
				+ "bar = b := 3"
				+ "END";*/
		
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);
		
		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		System.out.println(string);
		
		DefinitionsEliminator trans = new DefinitionsEliminator(startNode);
		startNode.apply(trans);
		
		final Ast2String ast2String2 = new Ast2String();
		startNode.apply(ast2String2);
		System.out.println(ast2String2.toString());
		
		MachineDeclarationsCollector c = new MachineDeclarationsCollector(startNode);
		
		final ScopeChecker checker = new ScopeChecker(c, null);
		
		//final Typechecker typechecker = new Typechecker(checker.getDefinedIdentifier());
		//startNode.apply(typechecker);
		
		//Hashtable<Node, BType> types = typechecker.type;
		//for (Entry<Node, BType> e : types.entrySet()) {
		//	System.out.println(e.getKey()+""+ e.getKey().getStartPos()+ " "+ e.getValue());
		//}
		
//		final TLAPrinter tlaPrinter= new TLAPrinter();
//		startNode.apply(tlaPrinter);
//		
//		System.out.println();
//		System.out.println(tlaPrinter.getStringbuilder());
		//System.out.println(typechecker.type);
		
	}

}
