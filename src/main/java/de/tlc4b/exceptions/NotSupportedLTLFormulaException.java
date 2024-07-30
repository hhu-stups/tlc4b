package de.tlc4b.exceptions;

public class NotSupportedLTLFormulaException extends TLC4BException {
	public NotSupportedLTLFormulaException(String message) {
		super(message);
	}

	public NotSupportedLTLFormulaException(String message, Throwable cause) {
		super(message, cause);
	}

	public NotSupportedLTLFormulaException(Throwable cause) {
		super(cause);
	}

	@Override
	public String getError() {
		return "NotSupportedLTLFormula";
	}
}
