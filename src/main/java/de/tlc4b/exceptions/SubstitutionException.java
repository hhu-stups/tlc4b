package de.tlc4b.exceptions;

public class SubstitutionException extends TLC4BException {

	public SubstitutionException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "SubstitutionError";
	}

}
