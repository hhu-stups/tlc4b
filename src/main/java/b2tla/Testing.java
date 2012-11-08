package b2tla;
import java.io.File;
import java.io.IOException;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class Testing {

	public static void main(String[] args) throws IOException, BException {
		int[] array = {1,2,3,4};
		System.out.println(array[4]);
		final BParser parser = new BParser("m");
		Start parse = parser.parseFile(new File("src/folder/M2.mch"), false);
	}
}
