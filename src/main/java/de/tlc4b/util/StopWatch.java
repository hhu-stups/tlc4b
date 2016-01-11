package de.tlc4b.util;

import java.util.Hashtable;

public class StopWatch {
	

	private static final Hashtable<Watches, Long> startTime = new Hashtable<Watches, Long>();
	private static final Hashtable<Watches, Long> runTime = new Hashtable<Watches, Long>();
	
	public enum Watches{
		PARSING_TIME, TRANSLATION_TIME, TLC_TIME, OVERALL_TIME, MODEL_CHECKING_TIME
	}
	
	public static void start(Watches watch){
		startTime.put(watch, System.currentTimeMillis());
	}
	
	public static long stop(Watches id) {
		long stopTime = System.currentTimeMillis()
				-  startTime.remove(id);
		runTime.put(id, stopTime);
		return stopTime;
	}
	
	public static long getRunTime(Watches id){
		return runTime.get(id);
	}
	
	public static String getRunTimeAsString(Watches id){
		return runTime.get(id).toString();
	}
}