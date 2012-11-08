package b2tla;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.pragma.Pragma;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;


public class Main {


	public static void main(String[] args) throws IOException, BException {

		
		String filename = "M1.mch";
		final File machineFile = new File(filename);
		//final String probfilename = filename.substring(0, dot) + ".prob";

		
		
		BParser parser = new BParser(filename);
		Start tree = parser.parseFile(machineFile, false);

		//System.out.println(parser.getDefinitions().getDefinitionNames());
		
		
		RecursiveMachineLoader r = new RecursiveMachineLoader(machineFile.getParent(), parser.getContentProvider());
		
		
		List<Pragma> pragmas = new ArrayList<Pragma>();
		pragmas.addAll(parser.getPragmas());
		r.loadAllMachines(machineFile, tree, parser.getSourcePositions(), parser.getDefinitions(), pragmas);
		
		r.printAsProlog(new PrintWriter(System.out), false);
		
		
//		//System.out.println(r.getParsedMachines());
//		System.out.println(r.getParsedMachines().size());
//		for (String name  : r.getParsedMachines().keySet()) {
//			System.out.print(name+ " ");
//			System.out.println(r.getParsedMachines().get(name));
//		}
		

	}

}
