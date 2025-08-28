package de.tlc4b.util;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public final class StopWatch {

	private static final Map<Watches, Long> startTime = new ConcurrentHashMap<>();
	private static final Map<Watches, Long> runTime = new ConcurrentHashMap<>();
	
	public enum Watches {
		PARSING_TIME, TRANSLATION_TIME, TLC_TIME, OVERALL_TIME, MODEL_CHECKING_TIME
	}

	private static long currentTime() {
		return System.currentTimeMillis();
	}

	public static void start(Watches watch) {
		startTime.put(watch, currentTime());
	}
	
	public static long stop(Watches id) {
		long stopTime = currentTime() - startTime.remove(id);
		runTime.put(id, stopTime);
		return stopTime;
	}
	
	public static long getRunTime(Watches id){
		return runTime.get(id);
	}
	
	public static String getRunTimeAsString(Watches id) {
		return String.valueOf(getRunTime(id));
	}
}
