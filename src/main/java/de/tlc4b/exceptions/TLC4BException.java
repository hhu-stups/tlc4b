package de.tlc4b.exceptions;

public abstract class TLC4BException extends RuntimeException {
	protected TLC4BException(String message) {
		super(message);
	}

	protected TLC4BException(String message, Throwable cause) {
		super(message, cause);
	}

	protected TLC4BException(Throwable cause) {
		super(cause);
	}

	public abstract String getError();
}
