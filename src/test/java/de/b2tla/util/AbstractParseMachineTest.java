package de.b2tla.util;

import java.io.File;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.Arrays;

import de.b2tla.tlc.TLCResults.TLCResult;
import de.b2tla.util.PolySuite.Configuration;

public abstract class AbstractParseMachineTest {

	private static final class MachineFilenameFilter implements FilenameFilter {
		private static final String[] MACHINE_SUFFIX = { ".mch" };

		public boolean accept(final File dir, final String name) {
			for (int i = 0; i < MACHINE_SUFFIX.length; i++) {
				if (name.endsWith(MACHINE_SUFFIX[i])) {
					return true;
				}
			}
			return false;
		}
	}

	protected static File[] getMachines(String path) {
		final File dir = new File(path);
		return dir.listFiles(new MachineFilenameFilter());
	}

	protected static Configuration getConfiguration(ArrayList<TestPair> list) {
		final ArrayList<File> allMachines = new ArrayList<File>();
		
		final ArrayList<TLCResult> expectedValues = new ArrayList<TLCResult>();
		for (TestPair testPair : list) {
			File[] machines = getMachines(testPair.getPath());
			allMachines.addAll(Arrays.asList(machines));
			for (int i = 0; i < machines.length; i++) {
				expectedValues.add(testPair.getResult());
			}
		}
		
		return new Configuration() {
			public int size() {
				return allMachines.size();
			}

			public File getTestValue(int index) {
				return allMachines.get(index);
			}

			public String getTestName(int index) {
				return allMachines.get(index).getName();
			}

			public TLCResult getExpectedValue(int index) {
				return expectedValues.get(index);
			}
		};
	}

}