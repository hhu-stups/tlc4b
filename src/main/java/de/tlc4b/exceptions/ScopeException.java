package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class ScopeException extends TLC4BException{

	public ScopeException(String e){
		super(e);
	}

	@Override
	public String getError() {
		return "ScopeException";
	}
	
}
