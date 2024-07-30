package de.tlc4b.exceptions;

public class TypeErrorException extends TLC4BException {
	public TypeErrorException(String message) {
		super(message);
	}

	public TypeErrorException(String message, Throwable cause) {
		super(message, cause);
	}

	public TypeErrorException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "TypeError";
	}
}
