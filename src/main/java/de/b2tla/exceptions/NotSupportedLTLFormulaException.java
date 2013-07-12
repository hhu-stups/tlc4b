package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class NotSupportedLTLFormulaException extends B2tlaException{

	public NotSupportedLTLFormulaException(String e) {
		super(e);
	}

	@Override
	public String getError() {
		return "NotSupportedLTLFormula";
	}

}
