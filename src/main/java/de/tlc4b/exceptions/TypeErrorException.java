package de.tlc4b.exceptions;

public class TypeErrorException extends TLC4BException {

	public TypeErrorException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "TypeError";
	}
}
