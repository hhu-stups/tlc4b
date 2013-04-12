package de.b2tla.exceptions;

@SuppressWarnings("serial")
public abstract class B2tlaException extends RuntimeException {

	public B2tlaException(String e) {
		super(e);
	}

}
