package de.b2tla;

import java.io.IOException;

import de.be4.classicalb.core.parser.exceptions.BException;

public class TLCTester {

	
	public static void main(String[] args) throws IOException, BException{
		String[] a = new String[]{ ".\\src\\test\\resources\\error\\ParseError.mch"};
		B2TLA.main(a);
	}
}
