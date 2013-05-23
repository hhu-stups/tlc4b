package de.b2tla.util;

import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;

import de.b2tla.Globals;


public class BTLCPrintStream extends PrintStream {
	private final PrintStream console;
	private final ArrayList<String> array;
	public BTLCPrintStream() {
		super(new PipedOutputStream());
		this.console = System.out;
		this.array = new ArrayList<String>();
	}
	
	public void resetSystemOut(){
		System.setOut(console);
	}
	
	public String[] getArray(){
		return array.toArray(new String[array.size()]);
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		BTLCPrintStream my = new BTLCPrintStream();
		System.setOut(my);
		
		System.out.print("hallo");
	}

	@Override
	public void println(String str){
		synchronized (BTLCPrintStream.class){
			if(!Globals.tool){
			//	console.println(str);
			}
				
			array.add(str);
		}
	}
	@Override
	public void print(String str){
		synchronized (BTLCPrintStream.class){
			//console.println(str);
			array.add(str);
		}
	}
	
	
}
