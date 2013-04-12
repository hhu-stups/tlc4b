package de.b2tla;

import java.io.IOException;

import de.be4.classicalb.core.parser.exceptions.BException;

public class TLCTester {

	
	public static void main(String[] args) throws IOException, BException{
		String[] a = new String[]{"-tool", ".\\src\\test\\resources\\ForDistribution\\Counter.mch"};
		B2TLA.main(a);
	}
}
