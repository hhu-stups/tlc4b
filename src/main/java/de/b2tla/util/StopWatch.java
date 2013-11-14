package de.b2tla.util;

import java.util.Hashtable;

public class StopWatch {
	private static final Hashtable<String, Long> startTime = new Hashtable<String, Long>();
	private static final Hashtable<String, Long> runTime = new Hashtable<String, Long>();
	
	public static void start(String id) {
		startTime.put(id, new Long(System.currentTimeMillis()));
	}

	public static long stop(String id) {
		long stopTime = System.currentTimeMillis()
				- ((Long) startTime.remove(id)).longValue();
		runTime.put(id, stopTime);
		return stopTime;
	}
	
	public static long getRunTime(String id){
		return runTime.get(id);
	}
}