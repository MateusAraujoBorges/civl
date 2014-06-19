package edu.udel.cis.vsl.civl.dynamic.common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableDynamicScope;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Singleton;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

public class CommonSymbolicUtility implements SymbolicUtility {

	private SymbolicUniverse universe;

	private ModelFactory modelFactory;

	private IntObject zeroObj;

	private IntObject oneObj;

	private IntObject twoObj;

	private NumericExpression zero;

	private CIVLErrorLogger errorLogger;

	private SymbolicExpression sizeofFunction;

	private SymbolicTupleType dynamicType;

	/**
	 * The pointer value is a triple <s,v,r> where s identifies the dynamic
	 * scope, v identifies the variable within that scope, and r identifies a
	 * point within that variable. The type of s is scopeType, which is just a
	 * tuple wrapping a single integer which is the dynamic scope ID number. The
	 * type of v is integer; it is the (static) variable ID number for the
	 * variable in its scope. The type of r is ReferenceExpression from SARL.
	 */
	private SymbolicTupleType pointerType;

	/**
	 * Map from symbolic type to a canonic symbolic expression of that type.
	 */
	private Map<SymbolicType, SymbolicExpression> typeExpressionMap = new HashMap<>();

	/**
	 * TODO ???
	 */
	private Map<SymbolicType, NumericExpression> sizeofDynamicMap = new HashMap<>();

	private CIVLHeapType heapType;

	private SymbolicTupleType procType;

	private SymbolicTupleType scopeType;

	private SymbolicTupleType functionPointerType;

	public CommonSymbolicUtility(SymbolicUniverse universe,
			ModelFactory modelFactory, CIVLErrorLogger errLogger) {
		SymbolicType dynamicToIntType;

		this.universe = universe;
		this.modelFactory = modelFactory;
		this.errorLogger = errLogger;
		pointerType = modelFactory.pointerSymbolicType();
		dynamicType = modelFactory.dynamicSymbolicType();
		dynamicToIntType = universe.functionType(new Singleton<SymbolicType>(
				dynamicType), universe.integerType());
		sizeofFunction = universe.symbolicConstant(
				universe.stringObject("SIZEOF"), dynamicToIntType);
		sizeofFunction = universe.canonic(sizeofFunction);
		this.zeroObj = (IntObject) universe.canonic(universe.intObject(0));
		this.oneObj = (IntObject) universe.canonic(universe.intObject(1));
		this.twoObj = (IntObject) universe.canonic(universe.intObject(2));
		zero = (NumericExpression) universe.canonic(universe.integer(0));
		this.heapType = modelFactory.heapType();
		this.procType = this.modelFactory.processSymbolicType();
		this.scopeType = this.modelFactory.scopeSymbolicType();
		this.functionPointerType = modelFactory.functionPointerSymbolicType();
	}

	@Override
	public int extractInt(CIVLSource source, NumericExpression expression) {
		IntegerNumber result = (IntegerNumber) universe
				.extractNumber(expression);

		// TODO make expression
		if (result == null)
			throw new CIVLInternalException(
					"Unable to extract concrete int from " + expression, source);
		return result.intValue();
	}

	@Override
	public int getScopeId(CIVLSource source, SymbolicExpression pointer) {
		return modelFactory.getScopeId(source,
				universe.tupleRead(pointer, zeroObj));
	}

	@Override
	public SymbolicExpression parentPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression symRef = getSymRef(pointer);

		if (symRef instanceof NTReferenceExpression)
			return setSymRef(pointer,
					((NTReferenceExpression) symRef).getParent());
		throw new CIVLInternalException("Expected non-trivial pointer: "
				+ pointer, source);
	}

	@Override
	public ReferenceExpression getSymRef(SymbolicExpression pointer) {
		SymbolicExpression result = universe.tupleRead(pointer, twoObj);

		assert result instanceof ReferenceExpression;
		return (ReferenceExpression) result;
	}

	@Override
	public SymbolicExpression setSymRef(SymbolicExpression pointer,
			ReferenceExpression symRef) {
		return universe.tupleWrite(pointer, twoObj, symRef);
	}

	@Override
	public int getVariableId(CIVLSource source, SymbolicExpression pointer) {
		return extractIntField(source, pointer, oneObj);
	}

	@Override
	public int extractIntField(CIVLSource source, SymbolicExpression tuple,
			IntObject fieldIndex) {
		NumericExpression field = (NumericExpression) universe.tupleRead(tuple,
				fieldIndex);

		return this.extractInt(source, field);
	}

	@Override
	public SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, String process, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		// if startIndex is zero and endIndex is length, return array
		// verify startIndex >=0 and endIndex<= Length
		// if startIndex==endIndex return emptyArray
		// else if startIndex and endIndex are concrete, create concrete array
		// else need array lambdas or subsequence operation: todo
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		NumericExpression length = universe.length(array);
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		SymbolicType elementType = arrayType.elementType();

		if (reasoner.isValid(universe.equals(zero, startIndex))
				&& reasoner.isValid(universe.equals(length, endIndex)))
			return array;
		else {
			BooleanExpression claim = universe.lessThanEquals(zero, startIndex);
			ResultType valid = reasoner.valid(claim).getResultType();

			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS, "negative start index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(endIndex, length);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"end index exceeds length of array");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			claim = universe.lessThanEquals(startIndex, endIndex);
			valid = reasoner.valid(claim).getResultType();
			if (valid != ResultType.YES) {
				state = errorLogger.logError(source, state, process,
						this.stateToString(state), claim, valid,
						ErrorKind.OUT_OF_BOUNDS,
						"start index greater than end index");
				pathCondition = state.getPathCondition();
				reasoner = universe.reasoner(pathCondition);
			}
			if (reasoner.isValid(universe.equals(startIndex, endIndex))) {
				return universe.emptyArray(elementType);
			} else {
				IntegerNumber concreteStart = (IntegerNumber) reasoner
						.extractNumber(startIndex);
				IntegerNumber concreteEnd = (IntegerNumber) reasoner
						.extractNumber(endIndex);

				if (concreteStart != null && concreteEnd != null) {
					int startInt = concreteStart.intValue();
					int endInt = concreteEnd.intValue();
					LinkedList<SymbolicExpression> valueList = new LinkedList<SymbolicExpression>();

					for (int i = startInt; i < endInt; i++)
						valueList.add(universe.arrayRead(array,
								universe.integer(i)));
					return universe.array(elementType, valueList);
				} else {
					NumericExpression subLength = universe.subtract(endIndex,
							startIndex);
					SymbolicCompleteArrayType subArrayType = universe
							.arrayType(elementType, subLength);
					NumericSymbolicConstant index = (NumericSymbolicConstant) universe
							.symbolicConstant(universe.stringObject("i"),
									universe.integerType());
					SymbolicExpression subArrayFunction = universe.lambda(
							index,
							universe.arrayRead(array,
									universe.add(startIndex, index)));

					return universe.arrayLambda(subArrayType, subArrayFunction);

				}
			}
		}
	}

	@Override
	public NumericExpression sizeof(CIVLSource source, SymbolicType type) {
		NumericExpression result = sizeofDynamicMap.get(type);

		if (result == null) {

			if (type.isBoolean())
				result = modelFactory.booleanType().getSizeof();
			else if (type == modelFactory.dynamicSymbolicType())
				result = modelFactory.dynamicType().getSizeof();
			else if (type.isInteger())
				result = modelFactory.integerType().getSizeof();
			else if (type == modelFactory.processSymbolicType())
				result = modelFactory.processType().getSizeof();
			else if (type.isReal())
				result = modelFactory.realType().getSizeof();
			else if (type == modelFactory.scopeSymbolicType())
				result = modelFactory.scopeType().getSizeof();
			else if (type instanceof SymbolicCompleteArrayType) {
				SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) type;

				result = sizeof(source, arrayType.elementType());
				result = universe.multiply(arrayType.extent(),
						(NumericExpression) result);
			} else if (type instanceof SymbolicArrayType) {
				throw new CIVLInternalException(
						"sizeof applied to incomplete array type", source);
			} else {
				// wrap the type in an expression of type dynamicTYpe
				SymbolicExpression typeExpr = expressionOfType(type);

				result = (NumericExpression) universe.apply(sizeofFunction,
						new Singleton<SymbolicExpression>(typeExpr));
			}
			sizeofDynamicMap.put(type, result);
		}
		return result;
	}

	@Override
	public SymbolicExpression expressionOfType(SymbolicType type) {
		SymbolicExpression result;

		type = (SymbolicType) universe.canonic(type);
		result = typeExpressionMap.get(type);
		if (result == null) {
			SymbolicExpression id = universe.integer(type.id());

			result = universe.canonic(universe.tuple(dynamicType,
					new Singleton<SymbolicExpression>(id)));
			typeExpressionMap.put(type, result);
		}
		return result;
	}

	@Override
	public SymbolicExpression sizeofFunction() {
		return this.sizeofFunction;
	}

	@Override
	public SymbolicExpression initialHeapValue() {
		return modelFactory.heapType().getInitialValue();
	}
	
	@Override
	public boolean isEmptyHeap(SymbolicExpression heapValue) {
		if (heapValue.isNull())
			return true;
		else {
			SymbolicSequence<?> heapFields = (SymbolicSequence<?>) heapValue
					.argument(0);
			int count = heapFields.size();

			for (int i = 0; i < count; i++) {
				SymbolicExpression heapField = heapFields.get(i);
				SymbolicSequence<?> heapFieldObjets = (SymbolicSequence<?>) heapField
						.argument(0);
				int size = heapFieldObjets.size();

				for (int j = 0; j < size; j++) {
					SymbolicExpression heapFieldObj = heapFieldObjets.get(j);
					SymbolicObject heapFieldObjValue = heapFieldObj.argument(0);

					if (heapFieldObjValue.symbolicObjectKind() == SymbolicObjectKind.STRING) {
						String value = ((StringObject) heapFieldObjValue)
								.getString();

						if (value.equals("UNDEFINED"))
							continue;
					}
					return false;
				}
			}
		}
		return true;
	}

	@Override
	public SymbolicExpression makePointer(int scopeId, int varId,
			ReferenceExpression symRef) {
		SymbolicExpression scopeField = modelFactory.scopeValue(scopeId);
		SymbolicExpression varField = universe.integer(varId);
		SymbolicExpression result = universe.tuple(
				pointerType,
				Arrays.asList(new SymbolicExpression[] { scopeField, varField,
						symRef }));

		return result;
	}

	public String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression) {
		return this.symbolicExpressionToString(source, state,
				symbolicExpression, false);
	}

	/**
	 * Obtains the string representation of a symbolic expression which is a
	 * pointer.
	 * 
	 * @param source
	 *            The source code element of the symbolic expression
	 * @param state
	 *            The state that the given symbolic expression belongs to
	 * @param pointer
	 *            The symbolic expression that is to be evaluated
	 * @return the string representation of a symbolic expression which is a
	 *         pointer
	 */
	private String functionPointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else if (pointer.operator() != SymbolicOperator.CONCRETE)
			return pointer.toString();
		else {
			int dyscopeId = getScopeId(source, pointer);
			if (dyscopeId < 0)
				return "UNDEFINED";
			else {
				DynamicScope dyScope = state.getScope(dyscopeId);
				SymbolicExpression funcNameExpression = universe.tupleRead(
						pointer, oneObj);
				StringBuffer funcName = this.charArrayToString(source,
						(SymbolicSequence<?>) funcNameExpression.argument(0),
						0, true);
				StringBuffer result = new StringBuffer();

				result.append('&');
				result.append("<");
				result.append("scope ");
				result.append(dyScope.lexicalScope().id());
				result.append(">(function)");
				result.append(funcName);
				return result.toString();
			}
		}
	}

	/**
	 * <p>
	 * Obtains the string representation of a symbolic expression, making
	 * pointers represented in a user-friendly way.
	 * </p>
	 * If a pointer is pointing to
	 * <ul>
	 * <li>
	 * 
	 * <pre>
	 * a variable: & variable &lt;dyscope name>;
	 * e.g., int a = 9; int * p = &a;
	 * then the representation of p would be &a&lt;d0> assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * an element of an array: &array<dyscope name>[index];
	 * e.g., int a[5]; int *p = &a[1];
	 * then the representation of p would be &a&lt;d0>[1] assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * a field of a struct: &struct&lt;dyscope name>.field;
	 * e.g., typedef struct {int x; int y;} A; A s; int*p = &s.y;
	 * then the representation of p would be &a&lt;d0>.y assuming that the name of the dynamic scope of a is d0.
	 * </pre>
	 * 
	 * </li>
	 * <li>
	 * 
	 * <pre>
	 * a heap cell: heapObject&lt;dyscope name, malloc ID, number of malloc call>.
	 * </pre>
	 * 
	 * </li>
	 * </ul>
	 * 
	 * @param source
	 *            The source code element of the symbolic expression.
	 * @param state
	 *            The state where the given symbolic expression is evaluated
	 *            from.
	 * @param symbolicExpression
	 *            The symbolic expression whose string representation is to be
	 *            obtained.
	 * @param atomize
	 *            True iff this is an atomic symbolic expression.
	 * @return The string representation of the given symbolic expression
	 * @throws UnsatisfiablePathConditionException
	 */
	private String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression, boolean atomize) {
		StringBuffer result = new StringBuffer();
		SymbolicType type = symbolicExpression.type();
		SymbolicType charType = modelFactory.charType()
				.getDynamicType(universe);

		if (type == null)
			return "NULL";
		else if (type.equals(this.pointerType)) {
			return pointerValueToString(source, state, symbolicExpression);
		} else if (type.equals(this.functionPointerType)) {
			return functionPointerValueToString(source, state,
					symbolicExpression);
		} else if (symbolicExpression.operator() == SymbolicOperator.CONCRETE
				&& type instanceof SymbolicArrayType
				&& ((SymbolicArrayType) type).elementType().equals(charType)) {
			result.append("\"");
			result.append(this.charArrayToString(source,
					(SymbolicSequence<?>) symbolicExpression.argument(0), 0,
					true));
			result.append("\"");
			return result.toString();
		} else if (type.equals(procType)) {
			int pid = modelFactory.getProcessId(source, symbolicExpression);

			if (!modelFactory.isPocessIdDefined(pid)) {
				return "UNDEFINED";
			}
			if (pid < 0)
				return "$proc_null";
			else {
				ProcessState procState = state.getProcessState(pid);

				if (procState == null)
					return "UNDEFINED";
				return procState.name();
			}
		} else if (type.equals(scopeType)) {
			int scopeId = modelFactory.getScopeId(source, symbolicExpression);

			if (!modelFactory.isScopeIdDefined(scopeId))
				return "UNDEFINED";
			if (scopeId < 0)
				return "$scope_null";
			else
				return state.getScope(scopeId).name();
		} else {
			SymbolicOperator operator = symbolicExpression.operator();
			SymbolicObject[] arguments = symbolicExpression.arguments();

			switch (operator) {
			case ADD:
				processFlexibleBinary(source, state, symbolicExpression,
						result, "+", false, atomize);
				return result.toString();
			case AND:
				processFlexibleBinary(source, state, symbolicExpression,
						result, " && ", true, atomize);
				return result.toString();
			case APPLY: {
				result.append(arguments[0].toStringBuffer(true));
				result.append("(");
				accumulate(source, state, result, ",",
						(SymbolicCollection<?>) arguments[1], false);
				result.append(")");
				return result.toString();
			}
			case ARRAY_LAMBDA:
				return symbolicExpression.toStringBufferLong().toString();
			case ARRAY_READ:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				result.append(arguments[1].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case ARRAY_WRITE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				result.append(arguments[1].toStringBuffer(false));
				result.append(":=");
				result.append(arguments[2].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case CAST:
				result.append('(');
				result.append(type.toStringBuffer(false));
				result.append(')');
				result.append(arguments[0].toStringBuffer(true));
				return result.toString();
			case CONCRETE: {
				SymbolicTypeKind tk = type.typeKind();

				if (tk == SymbolicTypeKind.CHAR) {
					result.append("'");
					result.append(arguments[0].toStringBuffer(false));
					result.append("'");
				} else {
					if (!type.isNumeric() && !type.isBoolean()) {
						if (tk == SymbolicTypeKind.TUPLE)
							result.append(type.toStringBuffer(false));
						else {
							result.append('(');
							result.append(type.toStringBuffer(false));
							result.append(')');
						}
					}
					{
						SymbolicObjectKind objectKind = arguments[0]
								.symbolicObjectKind();

						if (objectKind == SymbolicObjectKind.EXPRESSION_COLLECTION) {
							@SuppressWarnings("unchecked")
							SymbolicCollection<? extends SymbolicExpression> symbolicCollection = (SymbolicCollection<? extends SymbolicExpression>) arguments[0];

							result.append("<");
							for (SymbolicExpression symbolicElement : symbolicCollection) {
								result.append(symbolicExpressionToString(
										source, state, symbolicElement, false));
								result.append(",");
							}
							result.deleteCharAt(result.length() - 1);
							result.append(">");
						} else {
							result.append(arguments[0].toStringBuffer(false));
						}

					}
					if (type.isHerbrand())
						result.append('h');
				}
				return result.toString();
			}
			case COND:
				result.append(arguments[0].toStringBuffer(true));
				result.append(" ? ");
				result.append(arguments[1].toStringBuffer(true));
				result.append(" : ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case DENSE_ARRAY_WRITE: {
				int count = 0;
				boolean first = true;

				result.append(arguments[0].toStringBuffer(true));
				result.append("[");
				for (SymbolicExpression value : (SymbolicSequence<?>) arguments[1]) {
					if (!value.isNull()) {
						if (first)
							first = false;
						else
							result.append(", ");
						result.append(count + ":=");
						result.append(symbolicExpressionToString(source, state,
								value, false));
						// result.append(value.toStringBuffer(false));
					}
					count++;
				}
				result.append("]");
				return result.toString();
			}
			case DENSE_TUPLE_WRITE: {
				int count = 0;
				boolean first = true;

				result.append(arguments[0].toStringBuffer(true));
				result.append("<");
				for (SymbolicExpression value : (SymbolicSequence<?>) arguments[1]) {
					if (!value.isNull()) {
						if (first)
							first = false;
						else
							result.append(", ");
						result.append(count + ":=");
						// result.append(value.toStringBuffer(false));
						result.append(symbolicExpressionToString(source, state,
								value, false));
					}
					count++;
				}
				result.append(">");
				return result.toString();
			}
			case DIVIDE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("/");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case EQUALS:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" == ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case EXISTS:
				result.append("exists ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case FORALL:
				result.append("forall ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case INT_DIVIDE: {
				result.append(arguments[0].toStringBuffer(true));
				// result.append("\u00F7");
				result.append(" div ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			}
			case LAMBDA:
				result.append("lambda ");
				result.append(arguments[0].toStringBuffer(false));
				result.append(" : ");
				result.append(((SymbolicExpression) arguments[0]).type()
						.toStringBuffer(false));
				result.append(" . ");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case LENGTH:
				result.append("length(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case LESS_THAN:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" < ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case LESS_THAN_EQUALS:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" <= ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case MODULO:
				result.append(arguments[0].toStringBuffer(true));
				result.append("%");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case MULTIPLY:
				processFlexibleBinary(source, state, symbolicExpression,
						result, "*", true, false);
				return result.toString();
			case NEGATIVE:
				result.append("-");
				result.append(arguments[0].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case NEQ:
				result.append(arguments[0].toStringBuffer(false));
				result.append(" != ");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case NOT:
				result.append("!");
				result.append(arguments[0].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case NULL:
				result.append("NULL");
				return result.toString();
			case OR:
				processFlexibleBinary(source, state, symbolicExpression,
						result, " || ", false, atomize);
				// if (atomize)
				// atomize(result);
				return result.toString();
			case POWER:
				result.append(arguments[0].toStringBuffer(true));
				result.append("^");
				result.append(arguments[1].toStringBuffer(true));
				if (atomize)
					atomize(result);
				return result.toString();
			case SUBTRACT:
				processBinary(result, " - ", arguments[0], arguments[1], true);
				if (atomize)
					atomize(result);
				return result.toString();
			case SYMBOLIC_CONSTANT:
				result.append(arguments[0].toStringBuffer(false));
				return result.toString();
			case TUPLE_READ:
				result.append(arguments[0].toStringBuffer(true));
				result.append(".");
				result.append(arguments[1].toStringBuffer(false));
				if (atomize)
					atomize(result);
				return result.toString();
			case TUPLE_WRITE:
				result.append(arguments[0].toStringBuffer(true));
				result.append("[.");
				result.append(arguments[1].toStringBuffer(false));
				result.append(":=");
				result.append(arguments[2].toStringBuffer(false));
				result.append("]");
				return result.toString();
			case UNION_EXTRACT:
				result.append("extract(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case UNION_INJECT:
				result.append("inject(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			case UNION_TEST:
				result.append("test(");
				result.append(arguments[0].toStringBuffer(false));
				result.append(",");
				result.append(arguments[1].toStringBuffer(false));
				result.append(")");
				return result.toString();
			default:
				return symbolicExpression.toStringBufferLong().toString();
			}
		}
	}

	/**
	 * Place parentheses around the string buffer.
	 * 
	 * @param buffer
	 *            a string buffer
	 */
	private void atomize(StringBuffer buffer) {
		buffer.insert(0, '(');
		buffer.append(')');
	}

	/**
	 * Obtains the string representation of a symbolic expression which is a
	 * pointer.
	 * 
	 * @param source
	 *            The source code element of the symbolic expression
	 * @param state
	 *            The state that the given symbolic expression belongs to
	 * @param pointer
	 *            The symbolic expression that is to be evaluated
	 * @return the string representation of a symbolic expression which is a
	 *         pointer
	 */
	private String pointerValueToString(CIVLSource source, State state,
			SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else if (pointer.operator() != SymbolicOperator.CONCRETE)
			return pointer.toString();
		else {
			SymbolicTupleType pointerType = (SymbolicTupleType) pointer.type();
			int dyscopeId, vid;

			if (!pointerType.name().getString().equalsIgnoreCase("pointer")) {
				return pointer.toString();
			}

			dyscopeId = getScopeId(source, pointer);
			vid = getVariableId(source, pointer);
			if (dyscopeId == -1 && vid == -1)
				return "NULL";
			if (dyscopeId < 0)
				return "UNDEFINED";
			else {
				DynamicScope dyscope = state.getScope(dyscopeId);
				Variable variable = dyscope.lexicalScope().variable(vid);
				ReferenceExpression reference = (ReferenceExpression) universe
						.tupleRead(pointer, this.twoObj);

				if (variable.type().equals(this.heapType)) {
					String resultString = heapObjectReferenceToString(source,
							dyscopeId, this.heapType, reference).third;

					return resultString;
				} else {
					StringBuffer result = new StringBuffer();

					result.append('&');
					result.append("<");
					result.append(dyscope.name());
					result.append('>');
					result.append(variable.name());
					result.append(referenceToString(source, variable.type(),
							reference).right);
					return result.toString();
				}
			}
		}
	}

	/**
	 * Obtains the string representation of a reference to a heap object or part
	 * of a heap object.
	 * 
	 * @param source
	 *            The source code element of the reference expression.
	 * @param dyscopeId
	 *            The dynamic scope ID that the heap belongs to.
	 * @param type
	 *            The static type of the expression being referenced.
	 * @param reference
	 *            The reference expression, could be:
	 *            <ol>
	 *            <li>identity reference</li>
	 *            <li>array element reference</li>
	 *            <li>tuple element reference</li>
	 *            </ol>
	 * @return the string representation of a reference to a heap object or part
	 *         of a heap object.
	 */
	private Triple<Integer, CIVLType, String> heapObjectReferenceToString(
			CIVLSource source, int dyscopeId, CIVLType type,
			ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference()) {
			result.append("&<d");
			result.append(dyscopeId);
			result.append(">");
			result.append("heap<");
			return new Triple<>(0, type, result.toString());
		} else if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectReferenceToString(
					source, dyscopeId, type, arrayEleRef.getParent());
			NumericExpression index = arrayEleRef.getIndex();

			switch (parentResult.first) {
			case 0:
				throw new CIVLInternalException("Unreachable", source);
			case 1:
				result.append(parentResult.third);
				result.append(index);
				result.append('>');
				return new Triple<>(2, parentResult.second, result.toString());
			case 2:
				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, parentResult.second, result.toString());
			default:
				CIVLType arrayEleType = ((CIVLArrayType) parentResult.second)
						.elementType();

				result.append(parentResult.third);
				result.append('[');
				result.append(index);
				result.append(']');
				return new Triple<>(-1, arrayEleType, result.toString());
			}
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleCompRef = (TupleComponentReference) reference;
			Triple<Integer, CIVLType, String> parentResult = heapObjectReferenceToString(
					source, dyscopeId, type, tupleCompRef.getParent());
			IntObject index = tupleCompRef.getIndex();

			switch (parentResult.first) {
			case 0:
				CIVLHeapType heapType = (CIVLHeapType) parentResult.second;
				int indexId = index.getInt();
				CIVLType heapObjType = heapType.getMalloc(indexId)
						.getStaticElementType();

				result.append(parentResult.third);
				// result.append("malloc id: ");
				result.append(index.getInt());
				result.append(',');
				return new Triple<>(1, heapObjType, result.toString());
			case 1:
			case 2:
				throw new CIVLInternalException("Unreachable", source);
			default:
				CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.second;
				StructOrUnionField field = structOrUnionType.getField(index
						.getInt());

				result.append(parentResult.third);
				result.append('.');
				result.append(field.name());
				return new Triple<>(-1, field.type(), result.toString());
			}
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	/**
	 * Obtains the string representation from a reference expression.
	 * 
	 * @param source
	 *            The source code element of the reference expression.
	 * @param type
	 *            The type of the expression being referenced.
	 * @param reference
	 *            The reference expression whose string representation is to be
	 *            obtained.
	 * @return The type of the remaining part, and the string representation of
	 *         the given reference expression.
	 */
	private Pair<CIVLType, String> referenceToString(CIVLSource source,
			CIVLType type, ReferenceExpression reference) {
		StringBuffer result = new StringBuffer();

		if (reference.isIdentityReference())
			return new Pair<>(type, result.toString());
		if (reference.isArrayElementReference()) {
			ArrayElementReference arrayEleRef = (ArrayElementReference) reference;
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, arrayEleRef.getParent());
			String parent = parentResult.right;
			CIVLType arrayEleType = ((CIVLArrayType) parentResult.left)
					.elementType();
			NumericExpression index = arrayEleRef.getIndex();

			result.append(parent);
			result.append('[');
			result.append(index);
			result.append(']');
			return new Pair<>(arrayEleType, result.toString());
		} else if (reference.isTupleComponentReference()) {
			TupleComponentReference tupleComponentRef = (TupleComponentReference) reference;
			IntObject index = tupleComponentRef.getIndex();
			Pair<CIVLType, String> parentResult = this.referenceToString(
					source, type, tupleComponentRef.getParent());
			String parent = parentResult.right;
			CIVLStructOrUnionType structOrUnionType = (CIVLStructOrUnionType) parentResult.left;
			StructOrUnionField field = structOrUnionType.getField(index
					.getInt());

			result.append(parent);
			result.append('.');
			result.append(field.name());
			return new Pair<CIVLType, String>(field.type(), result.toString());
		} else {
			throw new CIVLInternalException("Unreachable", source);
		}
	}

	/**
	 * Computes string representation of a binary operator expression
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param arg0
	 *            object to be represented
	 * @param arg1
	 *            object to be represented
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 *            necessary)?
	 */
	private void processBinary(StringBuffer buffer, String opString,
			SymbolicObject arg0, SymbolicObject arg1, boolean atomizeArgs) {
		buffer.append(arg0.toStringBuffer(atomizeArgs));
		buffer.append(opString);
		buffer.append(arg1.toStringBuffer(atomizeArgs));
	}

	/**
	 * Computes string representation of a binary operator expression that may
	 * take either one argument (a list of expressions) or two arguments.
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 *            necessary)?
	 * @param atomizeResult
	 *            should the final result be atomized?
	 */
	private void processFlexibleBinary(CIVLSource source, State state,
			SymbolicExpression symbolicExpression, StringBuffer buffer,
			String opString, boolean atomizeArgs, boolean atomizeResult) {
		SymbolicObject[] arguments = symbolicExpression.arguments();

		if (arguments.length == 1)
			accumulate(source, state, buffer, opString,
					(SymbolicCollection<?>) arguments[0], atomizeArgs);
		else
			processBinary(buffer, opString, arguments[0], arguments[1],
					atomizeArgs);
		if (atomizeResult) {
			buffer.insert(0, '(');
			buffer.append(')');
		}
	}

	/**
	 * accumulates the operator opString to every operand in the following
	 * format opString = " " + opString + " ";
	 * 
	 * @param buffer
	 *            string buffer to which computed result should be appended
	 * @param opString
	 *            the string representation of the operator, e.g. "+"
	 * @param operands
	 *            collection of Symbolic Objects
	 * @param atomizeArgs
	 *            should each argument be atomized (surrounded by parens if
	 */
	private void accumulate(CIVLSource source, State state,
			StringBuffer buffer, String opString,
			SymbolicCollection<?> operands, boolean atomizeArgs) {
		boolean first = true;

		for (SymbolicExpression arg : operands) {
			if (first)
				first = false;
			else
				buffer.append(opString);
			buffer.append(symbolicExpressionToString(source, state, arg, first));
		}
	}

	public StringBuffer stateToString(State state) {
		int numScopes = state.numScopes();
		int numProcs = state.numProcs();
		StringBuffer result = new StringBuffer();

		result.append("State " + state.identifier());
		result.append("\n");
		result.append("| Path condition\n");
		result.append("| | " + state.getPathCondition());
		result.append("\n");
		result.append("| Dynamic scopes\n");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) state
					.getScope(i);

			if (dyscope == null)
				result.append("| | dyscope - (id=" + i + "): null\n");
			else
				result.append(dynamicScopeToString(state, dyscope, "" + i,
						"| | "));
		}
		result.append("| Process states\n");
		for (int pid = 0; pid < numProcs; pid++) {
			ProcessState process = state.getProcessState(pid);

			if (process == null)
				result.append("| | process - (id=" + pid + "): null");
			else
				result.append(process.toStringBuffer("| | "));
		}
		return result;
	}

	/**
	 * Prints a dyscope to a given print stream.
	 * 
	 * @param out
	 *            The print stream to be used for printing.
	 * @param state
	 *            The state that the dyscope belongs to.
	 * @param dyscope
	 *            The dyscope to be printed.
	 * @param id
	 *            The ID of the dyscope.
	 * @param prefix
	 *            The prefix for printing.
	 */
	private StringBuffer dynamicScopeToString(State state,
			DynamicScope dyscope, String id, String prefix) {
		Scope lexicalScope = dyscope.lexicalScope();
		int numVars = lexicalScope.numVariables();
		// BitSet reachers = dyscope.getReachers();
		// int bitSetLength = reachers.length();
		// boolean first = true;
		StringBuffer result = new StringBuffer();

		result.append(prefix + "dyscope " + dyscope.name() + " (id=" + id
				+ ", parent=d" + dyscope.getParentIdentifier() + ", static="
				+ lexicalScope.id() + ")\n");
		// result.append(prefix + "| reachers = {");
		// for (int j = 0; j < bitSetLength; j++) {
		// if (reachers.get(j)) {
		// if (first)
		// first = false;
		// else
		// result.append(",");
		// result.append(j);
		// }
		// }
		// result.append("}\n");
		result.append(prefix + "| variables\n");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = dyscope.getValue(i);
			String varName = variable.name().name();

			if (varName.equals(ModelFactory.HEAP_VAR) && value.isNull()) {
				continue;
			} else if (varName.equals(ModelFactory.ATOMIC_LOCK_VARIABLE)
					&& (value.isNull() || modelFactory.isProcessDefined(variable.getSource(),
							value).isFalse())) {
				continue;
			}
			result.append(prefix + "| | " + variable.name() + " = ");
			result.append(symbolicExpressionToString(variable.getSource(),
					state, value));
			result.append("\n");
		}
		return result;
	}

	/**
	 * Given a symbolic expression of type array of char, returns a string
	 * representation. If it is a concrete array of char consisting of concrete
	 * characters, this will be the obvious string. Otherwise the result is
	 * something readable but unspecified.
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	public StringBuffer charArrayToString(CIVLSource source,
			SymbolicSequence<?> charArray, int startIndex, boolean forPrint) {
		StringBuffer result = new StringBuffer();
		int numChars = charArray.size();// ignoring the '\0' at the
													// end
		// of the string.
		// stringChars = new char[numChars -
		// int_arrayIndex];
		for (int j = startIndex; j < numChars; j++) {
			SymbolicExpression charExpr = charArray.get(j);
			Character theChar = universe.extractCharacter(charExpr);

			if (theChar == null)
				throw new CIVLUnimplementedFeatureException(
						"non-concrete character in string at position " + j,
						source);
			if (theChar != '\0') {
				if (forPrint) {
					String theCharToString;
					switch (theChar) {
					case '\u000C':
						theCharToString = "\\f";
						break;
					case '\u0007':
						theCharToString = "\\a";
						break;
					case '\b':
						theCharToString = "\\b";
						break;
					case '\n':
						theCharToString = "\\n";
						break;
					case '\t':
						theCharToString = "\\t";
						break;
					case '\r':
						theCharToString = "\\r";
						break;
					default:
						theCharToString = theChar.toString();
					}
					result.append(theCharToString);
				} else {
					result.append(theChar);
				}
			}
		}
		return result;
	}

	@Override
	public int getArrayIndex(CIVLSource source, SymbolicExpression charPointer) {
		int int_arrayIndex;

		if (charPointer.type() instanceof SymbolicArrayType) {
			int_arrayIndex = 0;
		} else {
			ArrayElementReference arrayRef = (ArrayElementReference) getSymRef(charPointer);
			NumericExpression arrayIndex = arrayRef.getIndex();
			int_arrayIndex = extractInt(source, arrayIndex);
		}
		return int_arrayIndex;
	}
}
