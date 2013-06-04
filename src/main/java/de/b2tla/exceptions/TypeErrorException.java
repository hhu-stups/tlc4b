package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class TypeErrorException extends B2tlaException {

	public TypeErrorException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "TypeError";
	}
}
