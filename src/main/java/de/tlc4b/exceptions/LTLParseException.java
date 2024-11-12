package de.tlc4b.exceptions;

public class LTLParseException extends TLC4BException {
	public LTLParseException(String message) {
		super(message);
	}

	public LTLParseException(String message, Throwable cause) {
		super(message, cause);
	}

	public LTLParseException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "LTLParseError";
	}
}
