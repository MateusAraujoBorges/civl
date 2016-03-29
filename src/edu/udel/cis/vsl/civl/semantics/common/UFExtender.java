package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.Arrays;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class UFExtender implements UnaryOperator<SymbolicExpression> {

	private String rootName;

	private UnaryOperator<SymbolicExpression> rootFunction;

	private SymbolicType inputType;

	private SymbolicType outputType;

	private ArrayList<SymbolicConstant> functions = new ArrayList<>();

	private SymbolicUniverse universe;

	public UFExtender(String rootName, SymbolicType inputType,
			SymbolicType outputType,
			UnaryOperator<SymbolicExpression> rootFunction) {
		this.rootName = rootName;
		this.rootFunction = rootFunction;
		this.inputType = inputType;
		this.outputType = outputType;
		functions.add(universe.symbolicConstant(universe.stringObject(rootName),
				universe.functionType(Arrays.asList(inputType), outputType)));
	}

	private SymbolicConstant getFunction(int i) {
		int n = functions.size();

		if (i >= n) {
			SymbolicFunctionType ftype = (SymbolicFunctionType) functions
					.get(n - 1).type();
			SymbolicType itype = ftype.inputTypes().getType(0);
			SymbolicType otype = ftype.outputType();

			for (int j = n; j <= i; j++) {
				SymbolicType itype2 = universe.arrayType(itype);
				SymbolicType otype2 = universe.arrayType(otype);
				SymbolicType ftype2 = universe
						.functionType(Arrays.asList(itype2), otype2);

				functions.add(universe.symbolicConstant(
						universe.stringObject(rootName + j), ftype2));
				itype = itype2;
				otype = otype2;
			}
		}
		return functions.get(i);
	}

	private SymbolicExpression extend(SymbolicExpression expr) {
		SymbolicOperator op = expr.operator();
		SymbolicType type = expr.type();

		// f(concrete) = rootFunction.apply(concrete)
		// f(a[j],i) = extend(a,i+1) [j]
		// f(a[j:=v],i) = f[j:=extend(v,i=1)]
		// ditto for dense array write
		// f(LAMBDA x.e) = lambda x.f(e)
		// f(TUPLE_READ) =
		// f(ARRAY(e1,e2,...))
		// f(TUPLE(e1,e2,...))
		// f(ARRAY_LAMBDA)

		// default:
		// f(x) = APPLY appropriate function to x

		switch (op) {
		case CONCRETE:
			// return function;

		}
		return null;
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		// TODO Auto-generated method stub
		return null;
	}

}
