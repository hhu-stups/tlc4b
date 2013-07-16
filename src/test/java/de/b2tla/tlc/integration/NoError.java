package de.b2tla.tlc.integration;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.b2tla.util.*;
import de.b2tla.util.PolySuite.Config;
import de.b2tla.util.PolySuite.Configuration;

import de.b2tla.B2TLA;
import de.b2tla.B2TLAGlobals;
import de.b2tla.tlc.TLCOutput;


@RunWith(PolySuite.class)
public class NoError extends AbstractParseMachineTest{

	private static final String PATH = "../probprivate/public_examples/TLC/NoError";
	
	private final File machine;
	
	public NoError(File machine){
		this.machine = machine;
	}
	
	@Test
	public void testRunTLC() throws Exception {
		String[] a = new String[] {machine.getPath()};
		B2TLAGlobals.setDeleteOnExit(true);
		assertEquals(TLCOutput.ERROR.NoError, B2TLA.test(a));
	}
	

	@Config
	public static Configuration getConfig() {
		final File[] machines = getMachines(PATH);
		return new Configuration() {

			public int size() {
				return machines.length;
			}

			public File getTestValue(int index) {
				return machines[index];
			}

			public String getTestName(int index) {
				return machines[index].getName();
			}
		};
	}
	
}
