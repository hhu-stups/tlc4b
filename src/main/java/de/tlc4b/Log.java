package de.tlc4b;

import static de.tlc4b.util.StopWatch.Watches.PARSING_TIME;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.tlc4b.tlc.TLCResults;
import de.tlc4b.util.StopWatch;
import de.tlc4b.util.StopWatch.Watches;

public class Log {

	public static final String DELIMITER = ";";

	private final List<String> fieldNames = new ArrayList<>();
	private final List<String> fieldValues = new ArrayList<>();

	public Log(TLC4B tlc4b, TLCResults tlcResults) {
		fieldNames.add("Machine File");
		String machineFile = tlc4b.getMainFile().getAbsolutePath();
		fieldValues.add(machineFile);

		fieldNames.add("TLC Model Checking Time (s)");
		double tlcModelCheckingTime = tlcResults.getModelCheckingTime();
		fieldValues.add(String.valueOf(tlcModelCheckingTime));

		fieldNames.add("Parsing Time Of B machine (ms)");
		long parseTime = StopWatch.getRunTime(PARSING_TIME);
		fieldValues.add(String.valueOf(parseTime));

		fieldNames.add("Translation Time (ms)");
		long translationTime = StopWatch.getRunTime(Watches.TRANSLATION_TIME);
		fieldValues.add(String.valueOf(translationTime));

		fieldNames.add("Model Checking Time (ms)");
		long modelCheckingTime = StopWatch.getRunTime(Watches.MODEL_CHECKING_TIME);
		fieldValues.add(String.valueOf(modelCheckingTime));
		
		fieldNames.add("TLC Result");
		fieldValues.add(tlcResults.getResultString());

		fieldNames.add("States analysed");
		fieldValues.add(Integer.toString(tlcResults.getNumberOfDistinctStates()));

		fieldNames.add("Transitions fired");
		fieldValues.add(Integer.toString(tlcResults.getNumberOfTransitions()));

		fieldNames.add("Violated Definition");
		String violatedDefinition = tlcResults.getViolatedDefinition();
		fieldValues.add(violatedDefinition != null ? violatedDefinition : "");

		fieldNames.add("Violated Assertions");
		List<String> violatedAssertions = tlcResults.getViolatedAssertions();
		fieldValues.add(!violatedAssertions.isEmpty() ? String.join(DELIMITER, violatedAssertions) : "");

		fieldNames.add("Operation Coverage");
		Map<String, Long> operationCount = tlcResults.getOperationCount();
		List<String> opCountString = new ArrayList<>();
		if (operationCount != null) {
			operationCount.forEach((operation, count) -> opCountString.add(operation + DELIMITER + count));
		}
		fieldValues.add(!opCountString.isEmpty() ? String.join(DELIMITER, opCountString) : "");

		fieldNames.add("Trace File");
		fieldValues.add(tlc4b.getTraceFile() != null ? tlc4b.getTraceFile().getAbsolutePath() : "");
	}

	public String getCSVString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < fieldNames.size(); i++) {
			sb.append(fieldNames.get(i)).append(DELIMITER).append(fieldValues.get(i)).append("\n");
		}
		return sb.toString();
	}

}
