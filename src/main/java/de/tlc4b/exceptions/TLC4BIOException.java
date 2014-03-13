package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class TLC4BIOException extends TLC4BException{

	public TLC4BIOException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "I/O Error";
	}

}
