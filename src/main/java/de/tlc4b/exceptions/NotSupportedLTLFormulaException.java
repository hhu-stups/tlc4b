package de.tlc4b.exceptions;

public class NotSupportedLTLFormulaException extends TLC4BException {

	public NotSupportedLTLFormulaException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "NotSupportedLTLFormula";
	}

}
