package de.tlc4b.util;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.PolySuite.Configuration;

public abstract class AbstractParseMachineTest {
	private static final String MCH_SUFFIX = ".mch";

	protected static File[] getMachines(String path) {
		return new File(path).listFiles((dir, name) -> name.endsWith(MCH_SUFFIX));
	}

	protected static List<File> getMachinesRecursively(String path) {
		File root = new File(path);
		File[] list = root.listFiles();
		
		List<File> files = new ArrayList<>();
		if (list == null)
			return files;

		for (File f : list) {
			if (f.isDirectory()) {
				files.addAll(getMachinesRecursively(f.getAbsolutePath()));
			} else {
				String name = f.getName();
				if (name.endsWith(MCH_SUFFIX)) {
					files.add(f);
				}
			}
		}
		return files;
	}

	protected static Configuration getConfiguration2(List<String> list) {
		List<File> allMachines = new ArrayList<>();

		List<TLCResult> expectedValues = new ArrayList<>();
		for (String path : list) {
			List<File> machines = getMachinesRecursively(path);
			allMachines.addAll(machines);
			for (int i = 0; i < machines.size(); i++) {
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

	protected static Configuration getConfiguration(List<TestPair> list) {
		List<File> allMachines = new ArrayList<>();

		List<TLCResult> expectedValues = new ArrayList<>();
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