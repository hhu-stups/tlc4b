package standard;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import analysis.Ast2String;
import analysis.MachineContext;
import analysis.MachineDeclarationsCollector;
import analysis.ScopeChecker;
import analysis.Typechecker;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.pragma.Pragma;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class CompoundScopeTest {

	@Test
	public void test() throws BException, IOException {
		String filename = "src/test/resources/M1.mch";
		checkScope(filename);
	}

	public void checkScope(String filename) throws BException, IOException {
		
		final File machineFile = new File(filename);
		
		BParser parser = new BParser(filename);
		Start tree = parser.parseFile(machineFile, false);

		RecursiveMachineLoader r = new RecursiveMachineLoader(machineFile.getParent(), parser.getContentProvider());
		
		
		List<Pragma> pragmas = new ArrayList<Pragma>();
		pragmas.addAll(parser.getPragmas());
		r.loadAllMachines(machineFile, tree, parser.getSourcePositions(), parser.getDefinitions(), pragmas);
		//r.printAsProlog(new PrintWriter(System.out), false);
		
		Map<String, Start> map = r.getParsedMachines();
		ArrayList<String> list = new ArrayList<String>(map.keySet());
		
		
		Hashtable<String, MachineContext> machineContextsTable = new Hashtable<String, MachineContext>();
		Hashtable<String, Typechecker> typecheckerTable = new Hashtable<String, Typechecker>();
		for (int i = 0; i < list.size(); i++) {
			String name = list.get(i);
			//System.out.println(name);
			Start start = map.get(name);
			final Ast2String ast2String2 = new Ast2String();
			start.apply(ast2String2);
			System.out.println(ast2String2.toString());
			
			MachineContext c = new MachineContext(start, machineContextsTable);
			machineContextsTable.put(name, c);
			
		}
		
		
	}
}
