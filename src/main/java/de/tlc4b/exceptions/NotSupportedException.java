package de.tlc4b.exceptions;

public class NotSupportedException extends TLC4BException {
	public NotSupportedException(String message) {
		super(message);
	}

	public NotSupportedException(String message, Throwable cause) {
		super(message, cause);
	}

	public NotSupportedException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "NotSupportedException";
	}
}
