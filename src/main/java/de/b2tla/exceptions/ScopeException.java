package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class ScopeException extends B2tlaException{

	public ScopeException(String e){
		super(e);
	}

	@Override
	public String getError() {
		return "ScopeException";
	}
	
}
