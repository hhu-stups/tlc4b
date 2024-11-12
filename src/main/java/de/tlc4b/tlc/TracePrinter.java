package de.tlc4b.tlc;

import java.util.ArrayList;
import java.util.List;

import de.tlc4b.btypes.BType;
import de.tlc4b.btypes.FunctionType;
import de.tlc4b.btypes.PairType;
import de.tlc4b.btypes.SetType;
import de.tlc4b.btypes.StructType;
import de.tlc4b.exceptions.NotSupportedException;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.value.impl.*;
import util.UniqueString;
import static tlc2.value.ValueConstants.*;

public class TracePrinter {

	List<TLCStateInfo> trace;
	TLCState initialState;
	final TLCOutputInfo tlcOutputInfo;

	List<OpDeclNode> constants;
	List<OpDeclNode> variables;

	StringBuilder traceBuilder;

	public TracePrinter(List<TLCStateInfo> trace, TLCOutputInfo tlcOutputInfo) {
		this.trace = trace;
		this.tlcOutputInfo = tlcOutputInfo;

		constants = new ArrayList<>();
		variables = new ArrayList<>();
		for (int i = 0; i < TLCState.vars.length; i++) {
			String tlaName = TLCState.vars[i].getName().toString();
			String bName = tlcOutputInfo.getBName(tlaName);
			if (tlcOutputInfo.constants.contains(bName)) {
				constants.add(TLCState.vars[i]);
			} else {
				variables.add(TLCState.vars[i]);
			}
		}
		evalTrace();
	}

	public StringBuilder getTrace() {
		return traceBuilder;
	}

	private void evalTrace() {
		traceBuilder = new StringBuilder();

		if (trace != null) {
			traceBuilder.append(setupConstants(trace.get(0).state));
			for (int i = 0; i < trace.size(); i++) {
				if (i > 0) {
					traceBuilder.append("\n");
				}
				traceBuilder.append(evalExpression(trace.get(i).state));
			}
		} else {
			traceBuilder.append(setupConstants(initialState));
			traceBuilder.append(evalExpression(initialState));
		}

		// System.out.println(traceBuilder);
	}

	private StringBuilder setupConstants(TLCState state) {
		StringBuilder expression = new StringBuilder();
		if (tlcOutputInfo.constantSetup) {
			if (constants.isEmpty()) {
				expression.append("1 = 1");
			} else {
				for (int i = 0; i < constants.size(); i++) {
					if (i > 0) {
						expression.append(" & ");
					}
					UniqueString var = constants.get(i).getName();
					String bName = tlcOutputInfo.getBName(var.toString());
					BType type = tlcOutputInfo.getBType(var.toString());
					String value = parseValue((Value) state.lookup(var), type).toString();
					expression.append(bName).append(" = ").append(value);
				}
			}
			expression.append("\n");
		}
		return expression;
	}

	private StringBuilder evalExpression(TLCState state) {
		StringBuilder expression = new StringBuilder();

		for (int i = 0; i < variables.size(); i++) {
			if (i > 0) {
				expression.append(" & ");
			}
			UniqueString var = variables.get(i).getName();
			String bName = tlcOutputInfo.getBName(var.toString());
			BType type = tlcOutputInfo.getBType(var.toString());
			String value = parseValue((Value) state.lookup(var), type).toString();
			expression.append(bName).append(" = ").append(value);
		}
		return expression;
	}

	private StringBuilder parseValue(Value val, BType type) {
		// System.out.println(val.getClass());
		StringBuilder res = new StringBuilder();
		int valueType = val.getKind();
		switch (valueType) {
		case INTVALUE:
		case BOOLVALUE:
			return res.append(val);

		case INTERVALVALUE: {
			IntervalValue i = (IntervalValue) val;
			res.append("(");
			res.append(i.low).append("..").append(i.high);
			res.append(")");
			return res;
		}

		case SETENUMVALUE:
			SetType set = (SetType) type;
			res.append("{");
			res.append(parseValueVec(((SetEnumValue) val).elems,
					set.getSubtype()));
			res.append("}");
			return res;

		case TUPLEVALUE:
			if (type instanceof PairType) {
				BType first = ((PairType) type).getFirst();
				BType second = ((PairType) type).getSecond();
				res.append("(");
				res.append(parseValue(((TupleValue) val).elems[0], first));
				res.append(", ");
				res.append(parseValue(((TupleValue) val).elems[1], second));
				res.append(")");
				return res;
			} else if (type instanceof FunctionType) {
				if (((TupleValue) val).elems.length == 0) {
					res.append("{}");
				} else {
					BType subtype = ((FunctionType) type).getRange();
					res.append("[");
					res.append(parseEnumerationValue(((TupleValue) val).elems,
							subtype));
					res.append("]");
				}
				return res;

			}
			throw new NotSupportedException("Unknown type of tuple.");

		case RECORDVALUE: {
			RecordValue rec = (RecordValue) val;
			StructType struct = (StructType) type;
			res.append("rec(");
			for (int i = 0; i < rec.names.length; i++) {
				if (i > 0) {
					res.append(", ");
				}
				String name = rec.names[i].toString();
				BType t = struct.getType(name);
				res.append(name).append(" : ");
				res.append(parseValue(rec.values[i], t));
			}
			res.append(")");
			return res;
		}

		case FCNRCDVALUE:
			FcnRcdValue function = (FcnRcdValue) val;
			FunctionType funcType = (FunctionType) type;
			res.append("{");
			for (int i = 0; i < function.domain.length; i++) {
				if (i > 0) {
					res.append(", ");
				}
				res.append("(");
				res.append(parseValue(function.domain[i], funcType.getDomain()));
				res.append(", ");
				res.append(parseValue(function.values[i], funcType.getRange()));
				res.append(")");
			}
			res.append("}");
			return res;

		case MODELVALUE:
			ModelValue modelValue = (ModelValue) val;
			String bName = tlcOutputInfo.getBName(modelValue.toString());
			if (bName == null) {
				bName = modelValue.toString();
			}
			res.append(bName);
			return res;

		case SETOFTUPLESVALUE: {
			SetOfTuplesValue s = (SetOfTuplesValue) val;
			ValueEnumeration e = s.elements();
			return parseSetValue(res, s.size(), type, e);
		}

		case SETCUPVALUE: {
			SetCupValue s = (SetCupValue) val;
			ValueEnumeration e = s.elements();
			return parseSetValue(res, s.size(), type, e);
		}
		case SETCAPVALUE: {
			SetCapValue s = (SetCapValue) val;
			ValueEnumeration e = s.elements();
			return parseSetValue(res, s.size(), type, e);
		}

		case SETDIFFVALUE: {
			SetDiffValue s = (SetDiffValue) val;
			ValueEnumeration e = s.elements();
			return parseSetValue(res, s.size(), type, e);
		}

		case SUBSETVALUE: {
			SubsetValue s = (SubsetValue) val;
			SetType t = (SetType) type;
			res.append("POW(").append(parseValue(s.set, t.getSubtype()))
					.append(")");
			return res;
		}
		case UNIONVALUE: {
			UnionValue s = (UnionValue) val;
			SetType t = (SetType) type;
			res.append("union(");
			res.append(parseValue(s.set, new SetType(t)));
			res.append(")");
			return res;
		}

		case SETOFRCDSVALUE: {
			SetOfRcdsValue s = (SetOfRcdsValue) val;
			SetType t = (SetType) type;
			StructType struct = (StructType) t.getSubtype();
			res.append("struct(");
			for (int i = 0; i < s.names.length; i++) {
				if (i > 0) {
					res.append(", ");
				}
				res.append(s.names[i]);
				res.append(":");
				BType fieldType = struct.getType(s.names[i].toString());
				res.append(parseValue(s.values[i], new SetType(fieldType)));
			}
			res.append(")");
			return res;
		}

		case SETOFFCNSVALUE: {
			SetOfFcnsValue s = (SetOfFcnsValue) val;
			SetType t = (SetType) type;
			FunctionType func = (FunctionType) t.getSubtype();
			res.append("(");
			res.append(parseValue(s.domain, new SetType(func.getDomain())));
			res.append(" --> ");
			res.append(parseValue(s.range, new SetType(func.getRange())));
			res.append(")");
			return res;
		}

		case STRINGVALUE: {
			StringValue s = (StringValue) val;
			res.append("\"").append(s.getVal()).append("\"");
			return res;
		}

		case FCNLAMBDAVALUE: {
			FcnLambdaValue s = (FcnLambdaValue) val;
			res.append(parseValue(s.fcnRcd, type));
			return res;
		}
		case SETPREDVALUE: {
			SetPredValue s = (SetPredValue) val;
			res.append(parseValue(s.inVal, type));
			return res;
		}

		case LAZYVALUE: {
			LazyValue s = (LazyValue) val;
			res.append(parseValue(s.getValue(), type));
			return res;
		}

		}
		System.err.println("Type: " + val.getKind());
		throw new RuntimeException("not supported construct: " + val);
	}

	private StringBuilder parseSetValue(StringBuilder res, int size,
			BType type, ValueEnumeration e) {
		SetType t = (SetType) type;
		res.append("{");
		for (int i = 0; i < size; i++) {
			Value v = e.nextElement();
			if (i != 0) {
				res.append(", ");
			}
			if (v != null) {
				res.append(parseValue(v, t.getSubtype()));
			}
		}
		res.append("}");
		return res;
	}

	private StringBuilder parseValueVec(ValueVec elems, BType bType) {
		StringBuilder res = new StringBuilder();
		for (int i = 0; i < elems.size(); i++) {
			if (i > 0) {
				res.append(", ");
			}
			Value val = elems.elementAt(i);
			res.append(parseValue(val, bType));
		}
		return res;
	}

	private StringBuilder parseEnumerationValue(Value[] a, BType bType) {

		StringBuilder res = new StringBuilder();
		for (int i = 0; i < a.length; i++) {
			if (i > 0) {
				res.append(",");
			}
			res.append(parseValue(a[i], bType));
		}
		return res;
	}

}
