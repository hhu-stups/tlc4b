package de.tlc4b.tlc;

import java.util.ArrayList;

import de.tlc4b.btypes.BType;
import de.tlc4b.btypes.FunctionType;
import de.tlc4b.btypes.PairType;
import de.tlc4b.btypes.SetType;
import de.tlc4b.btypes.StructType;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.value.FcnLambdaValue;
import tlc2.value.FcnRcdValue;
import tlc2.value.IntervalValue;
import tlc2.value.LazyValue;
import tlc2.value.ModelValue;
import tlc2.value.RecordValue;
import tlc2.value.SetCapValue;
import tlc2.value.SetCupValue;
import tlc2.value.SetDiffValue;
import tlc2.value.SetEnumValue;
import tlc2.value.SetOfFcnsValue;
import tlc2.value.SetOfRcdsValue;
import tlc2.value.SetOfTuplesValue;
import tlc2.value.SetPredValue;
import tlc2.value.StringValue;
import tlc2.value.SubsetValue;
import tlc2.value.TupleValue;
import tlc2.value.UnionValue;
import tlc2.value.Value;
import tlc2.value.ValueVec;
import util.UniqueString;
import static tlc2.value.ValueConstants.*;

public class TracePrinter {

	ArrayList<TLCStateInfo> trace;
	TLCState initialState;
	TLCOutputInfo tlcOutputInfo;

	ArrayList<OpDeclNode> constants;
	ArrayList<OpDeclNode> variables;

	StringBuilder traceBuilder;

	public TracePrinter(ArrayList<TLCStateInfo> trace,
			TLCOutputInfo tlcOutputInfo) {
		this.trace = trace;
		this.tlcOutputInfo = tlcOutputInfo;

		constants = new ArrayList<OpDeclNode>();
		variables = new ArrayList<OpDeclNode>();
		for (int i = 0; i < TLCState.vars.length; i++) {
			String id = TLCState.vars[i].getName().toString();
			if (tlcOutputInfo.constants.contains(id)) {
				constants.add(TLCState.vars[i]);
			} else {
				variables.add(TLCState.vars[i]);
			}
		}

		evalTrace();
	}

	public TracePrinter(TLCState initialState, TLCOutputInfo tlcOutputInfo) {
		this.initialState = initialState;
		this.tlcOutputInfo = tlcOutputInfo;
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
			if(constants.size() == 0){
				expression.append("1 = 1");
			}else{
				for (int i = 0; i < constants.size(); i++) {
					if (i > 0) {
						expression.append(" & ");
					}
					UniqueString var = constants.get(i).getName();
					BType type = tlcOutputInfo.getBType(var.toString());
					String value = parseValue(state.lookup(var), type)
							.toString();
					expression.append(var).append(" = ").append(value);
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
			BType type = tlcOutputInfo.getBType(var.toString());
			String value = parseValue(state.lookup(var), type).toString();
			expression.append(var).append(" = ").append(value);
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
				BType subtype = ((FunctionType) type).getRange();
				res.append("[");
				res.append(parseEnumerationValue(((TupleValue) val).elems,
						subtype));
				res.append("]");
				return res;
			}
			return null;

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
			String BName = tlcOutputInfo.getBName(modelValue.toString());
			res.append(BName);
			return res;

		case SETOFTUPLESVALUE: {
			SetOfTuplesValue s = (SetOfTuplesValue) val;
			SetType t = (SetType) type;
			PairType pair = (PairType) t.getSubtype();
			res.append(parseValue(s.sets[0], new SetType(pair.getFirst())));
			res.append("*");
			res.append(parseValue(s.sets[1], new SetType(pair.getSecond())));
			return res;
		}

		case SETCUPVALUE: {
			SetCupValue s = (SetCupValue) val;
			res.append(parseValue(s.set1, type));
			res.append("\\/");
			res.append(parseValue(s.set2, type));
			return res;
		}
		case SETCAPVALUE: {
			SetCapValue s = (SetCapValue) val;
			res.append(parseValue(s.set1, type));
			res.append("/\\");
			res.append(parseValue(s.set2, type));
			return res;
		}

		case SETDIFFVALUE: {
			SetDiffValue s = (SetDiffValue) val;
			res.append(parseValue(s.set1, type));
			res.append("-");
			res.append(parseValue(s.set2, type));
			return res;
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
			res.append(parseValue(s.val, type));
			return res;
		}

		}
		System.err.println("Type: " + val.getKind());
		throw new RuntimeException("not supported construct: " + val);
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
