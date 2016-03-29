package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class extends certain kinds of operations on a type to compound symbolic
 * expressions.
 * 
 * @author siegel
 *
 */
public class UFExtender implements UnaryOperator<SymbolicExpression> {

	/**
	 * The name you want to use for the uninterpreted functions that will be
	 * created.
	 */
	private StringObject rootName;

	/**
	 * The primary operation which consumes an element of the given input type
	 * and returns something of the given output type. This operation should be
	 * defined everywhere, even if it just applies an uninterpreted functions
	 * most of the time.
	 */
	private UnaryOperator<SymbolicExpression> rootOperation;

	/**
	 * The input type of the root operation.
	 */
	private SymbolicType inputType;

	/**
	 * The output type of the root operation.
	 */
	private SymbolicType outputType;

	/**
	 * The uninterpreted functions that will be applied when necessary.
	 */
	private Map<SymbolicType, SymbolicConstant> uninterpretedFunctions = new HashMap<>();

	private SymbolicUniverse universe;

	public UFExtender(String rootName, SymbolicType inputType,
			SymbolicType outputType,
			UnaryOperator<SymbolicExpression> rootFunction) {
		this.rootName = universe.stringObject(rootName);
		this.rootOperation = rootFunction;
		this.inputType = inputType;
		this.outputType = outputType;
	}

	private SymbolicType newType(SymbolicType type) {
		if (inputType.equals(type))
			return outputType;
		switch (type.typeKind()) {
		case BOOLEAN:
		case CHAR:
		case INTEGER:
		case REAL:
			return type;
		case ARRAY: {
			SymbolicArrayType arrayType = (SymbolicArrayType) type;

			if (arrayType.isComplete())
				return universe.arrayType(newType(arrayType.elementType()),
						((SymbolicCompleteArrayType) arrayType).extent());
			else
				return universe.arrayType(newType(arrayType.elementType()));
		}
		case FUNCTION:
			// TODO

		case MAP:
			// TODO

		case SET:
			// TODO

		case TUPLE:
			// TODO

		case UNION:
			// TODO
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression expr) {
		SymbolicOperator op = expr.operator();
		SymbolicType type = expr.type();

		switch (op) {
		case ARRAY_READ:
			return universe.arrayRead(
					apply((SymbolicExpression) expr.argument(0)),
					(NumericExpression) expr.argument(1));
		case ARRAY_WRITE:
			return universe.arrayWrite(
					apply((SymbolicExpression) expr.argument(0)),
					(NumericExpression) expr.argument(1),
					apply((SymbolicExpression) expr.argument(2)));
		case DENSE_ARRAY_WRITE: {
			@SuppressWarnings("unchecked")
			SymbolicSequence<? extends SymbolicExpression> oldElements = (SymbolicSequence<? extends SymbolicExpression>) expr
					.argument(1);
			int size = oldElements.size();
			SymbolicExpression[] newElements = new SymbolicExpression[size];

			for (int i = 0; i < size; i++)
				newElements[i] = apply(oldElements.get(i));
			return universe.denseArrayWrite(
					apply((SymbolicExpression) expr.argument(0)),
					Arrays.asList(newElements));
		}
		case LAMBDA:
			return universe.lambda((SymbolicConstant) expr.argument(0),
					apply((SymbolicExpression) expr.argument(1)));
		case TUPLE_READ:
			return universe.tupleRead(
					apply((SymbolicExpression) expr.argument(0)),
					(IntObject) expr.argument(1));
		case ARRAY: {
			int n = expr.numArguments();
			SymbolicExpression[] newArgs = new SymbolicExpression[n];

			for (int i = 0; i < n; i++)
				newArgs[i] = apply((SymbolicExpression) expr.argument(i));
			return universe.array(
					newType(((SymbolicArrayType) type).elementType()), newArgs);
		}
		case TUPLE: {
			int n = expr.numArguments();
			SymbolicExpression[] newArgs = new SymbolicExpression[n];

			for (int i = 0; i < n; i++)
				newArgs[i] = apply((SymbolicExpression) expr.argument(i));
			return universe.tuple((SymbolicTupleType) newType(type), newArgs);
		}
		case ARRAY_LAMBDA:
			// TODO
		case COND:
			return universe.cond((BooleanExpression) expr.argument(0),
					apply((SymbolicExpression) expr.argument(1)),
					apply((SymbolicExpression) expr.argument(2)));
		default:
			if (type.equals(inputType))
				return rootOperation.apply(expr);

			SymbolicConstant f = uninterpretedFunctions.get(type);

			if (f == null) {
				f = universe.symbolicConstant(rootName,
						universe.functionType(Arrays.asList(type), outputType));
				uninterpretedFunctions.put(type, f);
			}
			return universe.apply(f, Arrays.asList(expr));
		}
	}

}
