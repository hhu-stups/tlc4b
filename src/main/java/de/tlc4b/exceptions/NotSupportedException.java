package de.tlc4b.exceptions;

@SuppressWarnings("serial")
public class NotSupportedException extends TLC4BException{

	
	public NotSupportedException(String e){
		super(e);
	}

	@Override
	public String getError() {
		return "NotSupportedException";
	}
}
