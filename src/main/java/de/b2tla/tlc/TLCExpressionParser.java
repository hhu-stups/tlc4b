package de.b2tla.tlc;

import java.util.Hashtable;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.b2tla.btypes.BType;
import de.b2tla.btypes.FunctionType;
import de.b2tla.btypes.PairType;
import de.b2tla.btypes.SetType;

public class TLCExpressionParser {

	private StringBuilder sb;
	private String string;
	private Hashtable<String, BType> types;

	public static String parseLine(String line) {
		TLCExpressionParser parser = new TLCExpressionParser(line, null);
		parser.parse();
		return parser.sb.toString();
	}

	public static String parseLine(String line, Hashtable<String, BType> types) {
		TLCExpressionParser parser = new TLCExpressionParser(line, types);
		parser.parse();
		return parser.sb.toString();
	}

	public TLCExpressionParser(String stringToTranslate,
			Hashtable<String, BType> t) {
		this.string = stringToTranslate;
		this.sb = new StringBuilder();
		this.types = t;
	}

	public void parse() {
		string = string.replaceAll("\\s", "");
		parsePredicate();
	}

	private BType getType(String var) {
		if (types != null) {
			return types.get(var);
		} else {
			return null;
		}
	}

	private void parsePredicate() throws MatchException {
		try {
			match("/\\");
		} catch (MatchException e) {
		}
		String var = parseIdentifier();
		BType varType = getType(var);
		replace("=", " = ");
		parseExpr(varType);

		while (comes("/\\")) {
			replace("/\\", " & ");
			String var2 = parseIdentifier();
			BType varType2 = getType(var2);
			replace("=", " = ");
			parseExpr(varType2);
		}
	}

	private void parseExpr(BType type) throws MatchException {
		if (comes("<<")) {
			parseTuple(type);
		} else if (parseNumber()) {
		} else if (null != parseIdentifier()) {
		} else if (comes("(")) {
			parseFunction(type);
		} else if (comes("{")) {
			parseSet(type);
		} else {
			throw new RuntimeException("Error while parsing trace. Can not parse: " + string);
		}
		return;
	}

	private void parseSet(BType type) throws MatchException {
		BType subtype = null;
		if (type != null) {
			subtype = ((SetType) type).getSubtype();
		}
		replace("{", "{");
		if (comes("}")) {
			replace("}", "}");
			return;
		}
		parseExpr(subtype);
		while (comes(",")) {
			replace(",", ",");
			parseExpr(subtype);
		}
		replace("}", "}");
	}

	private void parseFunction(BType type) throws MatchException {
		BType domain = null;
		BType range = null;
		if (type != null) {
			FunctionType f = (FunctionType) type;
			domain = f.getDomain();
			range = f.getRange();
		}

		replace("(", "{");
		sb.append("(");
		parseExpr(domain);
		replace(":>", ",");
		parseExpr(range);
		sb.append(")");

		while (comes("@@")) {
			replace("@@", ",");

			sb.append("(");
			parseExpr(domain);
			replace(":>", ",");
			parseExpr(range);
			sb.append(")");

		}
		replace(")", "}");
	}

	private String parseIdentifier() throws MatchException {
		Pattern Number = Pattern.compile("\\w+");
		Matcher matcher = Number.matcher(string);
		if (matcher.lookingAt()) {
			String res = matcher.group();
			sb.append(res);
			string = string.substring(matcher.end());
			return res;
		} else {
			return null;
		}
	}

	private boolean parseNumber() throws MatchException {
		Pattern Number = Pattern.compile("-?(\\d)+");
		Matcher matcher = Number.matcher(string);
		if (matcher.lookingAt()) {
			String res = matcher.group();
			sb.append(res);
			string = string.substring(matcher.end());
			return true;
		} else {
			return false;
		}
	}

	private void parseTuple(BType type) throws MatchException {
		if (!comes("<<")) {
			throw new MatchException();
		}
		boolean isSequence = true;
		BType first = null;
		BType second = null;
		if (type != null) {
			if (type instanceof PairType) {
				isSequence = false;
				first = ((PairType) type).getFirst();
				second = ((PairType) type).getSecond();
			} else if (type instanceof SetType) {
				isSequence = false;
				SetType set = (SetType) type;
				PairType pair = (PairType) set.getSubtype();
				first = pair.getSecond();
				second = pair.getSecond();
			} else {
				FunctionType f = (FunctionType) type;
				first = f.getRange();
				second = f.getRange();
			}
		}

		replace("<<", isSequence ? "[" : "(");
		if (comes(">>")) {
			replace(">>", isSequence ? "]" : ")");
			return;
		}else{
			parseExpr(first);
			while (comes(",")) {
				replace(",", ",");
				parseExpr(second);
			}
		}
		replace(">>", isSequence ? "]" : ")");
	}

	private boolean comes(String stringToMatch) {
		if (string.startsWith(stringToMatch)) {
			return true;
		} else {
			return false;
		}
	}

	private void replace(String stringToMatch, String replaceBy)
			throws MatchException {
		match(stringToMatch);
		sb.append(replaceBy);
	}

	private void match(String stringToMatch) throws MatchException {
		if (string.startsWith(stringToMatch)) {
			string = string.substring(stringToMatch.length());
		} else {
			throw new MatchException();
		}
	}

	class MatchException extends RuntimeException {
		private static final long serialVersionUID = 1L;
	}

}
