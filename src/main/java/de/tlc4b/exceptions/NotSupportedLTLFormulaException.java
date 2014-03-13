package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class NotSupportedLTLFormulaException extends TLC4BException{

	public NotSupportedLTLFormulaException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "NotSupportedLTLFormula";
	}

}
