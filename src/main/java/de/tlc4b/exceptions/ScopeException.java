package de.tlc4b.exceptions;

public class ScopeException extends TLC4BException {
	public ScopeException(String message) {
		super(message);
	}

	public ScopeException(String message, Throwable cause) {
		super(message, cause);
	}

	public ScopeException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "ScopeException";
	}
}
