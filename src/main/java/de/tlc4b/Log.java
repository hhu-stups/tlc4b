package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.PARSING_TIME;

import java.util.ArrayList;

import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;
import de.tlc4b.util.StopWatch.Watches;

public class Log {

	private final ArrayList<String> fieldNames = new ArrayList<>();
	private final ArrayList<String> fieldValues = new ArrayList<>();

	public Log(TLC4B tlc4b, TLCResults tlcResults) {

		fieldNames.add("Machine File");
		String machineFile = tlc4b.getMainFile().getAbsolutePath();
		fieldValues.add(machineFile);

		fieldNames.add("TLC Model Checking Time (s)");
		int tlcModelCheckingTime = tlcResults.getModelCheckingTime();
		fieldValues.add(String.valueOf(tlcModelCheckingTime));

		fieldNames.add("Parsing Time Of B machine (ms)");
		long parseTime = StopWatch.getRunTime(PARSING_TIME);
		fieldValues.add(String.valueOf(parseTime));

		fieldNames.add("Translation Time (ms)");
		long translationTime = StopWatch.getRunTime(Watches.TRANSLATION_TIME);
		fieldValues.add(String.valueOf(translationTime));

		fieldNames.add("Model Checking Time (ms)");
		long modelCheckingTime = StopWatch
				.getRunTime(Watches.MODEL_CHECKING_TIME);
		fieldValues.add(String.valueOf(modelCheckingTime));
		
		fieldNames.add("TLC Result");
		fieldValues.add(tlcResults.getResultString());
	}

	public String getCSVValueLine() {
		return getCSVLine(fieldValues);
	}

	public String getCSVFieldNamesLine() {
		return getCSVLine(fieldNames);
	}

	private String getCSVLine(ArrayList<String> list) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < list.size(); i++) {
			sb.append(list.get(i));
			if (i < list.size() - 1) {
				sb.append(";");
			}
		}
		sb.append("\n");
		return sb.toString();
	}

}
