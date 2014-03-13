package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class LTLParseException extends TLC4BException{

	public LTLParseException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "LTLParseError";
	}

}
