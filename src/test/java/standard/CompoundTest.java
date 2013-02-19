package standard;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.pragma.Pragma;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class CompoundTest {

	@Test
	public void test() throws IOException, BException {
		String filename = "src/test/resources/compound/M1.mch";
		//final int dot = filename.lastIndexOf('.');
		final File machineFile = new File(filename);
		//final String probfilename = filename.substring(0, dot) + ".prob";

		
		
		BParser parser = new BParser(filename);
		Start tree = parser.parseFile(machineFile, false);

		RecursiveMachineLoader r = new RecursiveMachineLoader(machineFile.getParent(), parser.getContentProvider());
		
		
		List<Pragma> pragmas = new ArrayList<Pragma>();
		pragmas.addAll(parser.getPragmas());
		r.loadAllMachines(machineFile, tree, parser.getSourcePositions(), parser.getDefinitions(), pragmas);
		
		r.printAsProlog(new PrintWriter(System.out), false);
	}

}
