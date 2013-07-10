package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class LTLParseException extends B2tlaException{

	public LTLParseException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "LTLParseError";
	}

}
