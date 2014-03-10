package de.b2tla.exceptions;

@SuppressWarnings("serial")
public class NotSupportedException extends B2tlaException{

	
	public NotSupportedException(String e){
		super(e);
	}

	@Override
	public String getError() {
		return "NotSupportedException";
	}
}
