package de.tlc4b.exceptions;

public class TranslationException extends TLC4BException {
	public TranslationException(String message) {
		super(message);
	}

	public TranslationException(String message, Throwable cause) {
		super(message, cause);
	}

	public TranslationException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "TranslationError";
	}
}
