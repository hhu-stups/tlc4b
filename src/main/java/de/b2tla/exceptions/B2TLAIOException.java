package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class B2TLAIOException extends B2tlaException{

	public B2TLAIOException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "I/O Error";
	}

}
