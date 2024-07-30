package de.tlc4b.util;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.tlc4b.tlc.TLCResults.TLCResult;
import de.tlc4b.util.PolySuite.Configuration;

public abstract class AbstractParseMachineTest {
	protected static Configuration getConfiguration2(List<String> list) {
		List<File> allMachines = new ArrayList<>();

		for (String path : list) {
			allMachines.addAll(TestUtil.getMachinesRecursively(path));
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
				return TLCResult.NoError;
			}
		};
	}

	protected static Configuration getConfiguration(List<String> list, TLCResult expectedResult) {
		List<File> allMachines = new ArrayList<>();

		for (String path : list) {
			allMachines.addAll(Arrays.asList(TestUtil.getMachines(path)));
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
				return expectedResult;
			}
		};
	}

}