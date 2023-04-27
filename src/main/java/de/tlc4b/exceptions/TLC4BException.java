package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public abstract class TLC4BException extends RuntimeException {

	public TLC4BException(String e) {
		super(e);
	}

	public abstract String getError();
	
}
