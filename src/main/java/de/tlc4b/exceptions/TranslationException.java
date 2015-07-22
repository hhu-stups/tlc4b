package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class TranslationException extends TLC4BException{

	public TranslationException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "TranslationError";
	}

}
