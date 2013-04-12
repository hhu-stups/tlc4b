package de.b2tla.prettyprint;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;


public class Tester {

	
	
	public Tester(String module, String config) {
		File moduleFile;
		moduleFile = new File("test.tla");
		try {
			moduleFile.createNewFile();
		} catch (IOException e) {
			System.err.println("Could not create File.");
			return;
		}
		Writer fw = null;
		try {
			String res = module;
			fw = new FileWriter(moduleFile);
			fw.write(res);
			fw.close();
			System.out.println("TLA Module test.tla created.");
		} catch (IOException e) {
			System.err.println("Error while creating file ");
		}
		
		File configFile;
		configFile = new File("test.cfg");
		try {
			configFile.createNewFile();
		} catch (IOException e) {
			System.err.println("Could not create File.");
			return;
		}
		Writer fw2 = null;
		try {
			String res = config;
			fw2 = new FileWriter(configFile);
			fw2.write(res);
			fw2.close();
			System.out.println("TLA Config test.cfg created.");
		} catch (IOException e) {
			System.err.println("Error while creating file ");
		}

	}

}
