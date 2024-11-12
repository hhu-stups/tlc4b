package de.tlc4b.exceptions;

public class SubstitutionException extends TLC4BException {
	public SubstitutionException(String message) {
		super(message);
	}

	public SubstitutionException(String message, Throwable cause) {
		super(message, cause);
	}

	public SubstitutionException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "SubstitutionError";
	}
}
