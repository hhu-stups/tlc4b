package de.tlc4b.util;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.PolySuite.Configuration;

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

	protected static File[] getMachinesRecursively(String path, ArrayList<String> ignoreList) {
		File[] files = walk(path, ignoreList).toArray(new File[0]);
		return files;
	}

	private static ArrayList<File> walk(String path, ArrayList<String> ignoreList) {
		File root = new File(path);
		File[] list = root.listFiles();
		
		ArrayList<File> files = new ArrayList<File>();
		if (list == null)
			return files;

		for (File f : list) {
			if (f.isDirectory()) {
				boolean visitDir = true;
				for (String string : ignoreList) {
					File ignore = new File(string);
					try {
						if(f.getCanonicalPath().equals(ignore.getCanonicalPath())){
							visitDir = false;
						}
					} catch (IOException e) {
						visitDir = false;
					}
				}
				if(visitDir){
					files.addAll(walk(f.getAbsolutePath(),ignoreList));
				}
				
			} else {
				String name =f.getName();
					if (name.endsWith(".mch")) {
						files.add(f);
					}
			}
		}
		return files;
	}

	protected static Configuration getConfiguration2(ArrayList<String> list, ArrayList<String> ignoreList) {
		final ArrayList<File> allMachines = new ArrayList<File>();

		final ArrayList<TLCResult> expectedValues = new ArrayList<TLCResult>();
		for (String path : list) {
			File[] machines = getMachinesRecursively(path, ignoreList);
			allMachines.addAll(Arrays.asList(machines));
			for (int i = 0; i < machines.length; i++) {
				expectedValues.add(TLCResult.NoError);
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