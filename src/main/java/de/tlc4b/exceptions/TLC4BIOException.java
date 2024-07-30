package de.tlc4b.exceptions;

public class TLC4BIOException extends TLC4BException {
	public TLC4BIOException(String message) {
		super(message);
	}

	public TLC4BIOException(String message, Throwable cause) {
		super(message, cause);
	}

	public TLC4BIOException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "I/O Error";
	}
}
