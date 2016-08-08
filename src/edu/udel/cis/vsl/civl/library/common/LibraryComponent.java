package edu.udel.cis.vsl.civl.library.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;

/**
 * The LibraryComponent class provides the common data and operations of library
 * evaluator, enabler, and executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class LibraryComponent {

	// The order of these operations should be consistent with civlc.cvh
	// file.
	/**
	 * Operators:
	 * 
	 * <pre>
	 *   _NO_OP,  // no operation
	 *   _MAX,    // maxinum
	 *   _MIN,    // minimun
	 *   _SUM,    // sum
	 *   _PROD,   // product
	 *   _LAND,   // logical and
	 *   _BAND,   // bit-wise and
	 *   _LOR,    // logical or
	 *   _BOR,    // bit-wise or
	 *   _LXOR,   // logical exclusive or
	 *   _BXOR,   // bit-wise exclusive or
	 *   _MINLOC, // min value and location
	 *   _MAXLOC, // max value and location
	 *   _REPLACE // replace ? TODO: Find definition for this operation
	 * </pre>
	 */
	protected enum CIVLOperator {
		CIVL_NO_OP, // no operation
		CIVL_MAX, // maxinum
		CIVL_MIN, // minimun
		CIVL_SUM, // sum
		CIVL_PROD, // product
		CIVL_LAND, // logical and
		CIVL_BAND, // bit-wise and
		CIVL_LOR, // logical or
		CIVL_BOR, // bit-wise or
		CIVL_LXOR, // logical exclusive or
		CIVL_BXOR, // bit-wise exclusive or
		CIVL_MINLOC, // min value and location
		CIVL_MAXLOC, // max value and location
		CIVL_REPLACE // replace ? TODO: Find definition for this operation
	}

	/**
	 * The symbolic expression of one.
	 */
	protected NumericExpression one;

	/**
	 * The symbolic object of integer one.
	 */
	protected IntObject oneObject;

	/**
	 * The symbolic expression of three.
	 */
	protected NumericExpression three;

	/**
	 * The symbolic object of integer three.
	 */
	protected IntObject threeObject;

	/**
	 * The symbolic expression of two.
	 */
	protected NumericExpression two;

	/**
	 * The symbolic object of integer two.
	 */
	protected IntObject twoObject;

	/**
	 * The symbolic expression of zero.
	 */
	protected NumericExpression zero;

	/**
	 * The symbolic object of integer zero.
	 */
	protected IntObject zeroObject;

	/**
	 * The symbolic universe for symbolic computations.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic universe for symbolic computations.
	 */
	protected SymbolicUtility symbolicUtil;

	/**
	 * The symbolic analyzer for operations on symbolic expressions and states.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	protected String name;

	protected BooleanExpression trueValue;
	protected BooleanExpression falseValue;

	protected LibraryEvaluatorLoader libEvaluatorLoader;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The static model of the program.
	 */
	protected Model model;

	protected CIVLTypeFactory typeFactory;

	/**
	 * The CIVL configuration object
	 */
	protected CIVLConfiguration civlConfig;

	protected CIVLErrorLogger errorLogger;

	protected Evaluator evaluator;

	/**
	 * Creates a new instance of a library.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer to be used.
	 */
	protected LibraryComponent(String name, SymbolicUniverse universe,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader,
			ModelFactory modelFactory, CIVLErrorLogger errLogger,
			Evaluator evaluator) {
		this.name = name;
		this.universe = universe;
		this.zero = universe.zeroInt();
		this.one = universe.oneInt();
		this.two = universe.integer(2);
		this.three = universe.integer(3);
		this.zeroObject = universe.intObject(0);
		this.oneObject = universe.intObject(1);
		this.twoObject = universe.intObject(2);
		this.threeObject = universe.intObject(3);
		this.symbolicUtil = symbolicUtil;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.trueValue = universe.trueExpression();
		this.falseValue = universe.falseExpression();
		this.libEvaluatorLoader = libEvaluatorLoader;
		this.modelFactory = modelFactory;
		this.model = modelFactory.model();
		this.typeFactory = modelFactory.typeFactory();
		this.civlConfig = civlConfig;
		this.errorLogger = errLogger;
		this.evaluator = evaluator;
	}

	/**
	 * Returns the name associated to this library executor or enabler, for
	 * example, "stdio".
	 * 
	 * @return
	 */
	public String name() {
		return this.name;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Apply a CIVL operation on a pair of operands.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The identifier of the current process
	 * @param process
	 *            The String identifier of the current process
	 * @param operands
	 *            An array of two operands: <code>{operand0, operand1}</code>
	 * @param CIVLOp
	 *            A integer code represents a CIVL operation
	 * @param count
	 *            The number of pairs of operands.
	 * @param elementType
	 *            The {@link SymbolicType} of elements of one operand
	 * @param countStep
	 *            The number of elements in one operand
	 * @param civlsource
	 *            The {@link CIVLSource} of this operation
	 * @return A {@link SymbolicExpression} results after the operation.
	 * @throws UnsatisfiablePathConditionException
	 *             when types of operands are invalid for operations.
	 */
	protected SymbolicExpression applyCIVLOperation(State state, int pid,
			String process, SymbolicExpression operands[], CIVLOperator CIVLOp,
			NumericExpression count, SymbolicType elementType,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		Number concCount = reasoner.extractNumber(count);
		SymbolicExpression operand0 = operands[0];
		SymbolicExpression operand1 = operands[1];
		int countStep = 1;

		if (CIVLOp == CIVLOperator.CIVL_MINLOC
				|| CIVLOp == CIVLOperator.CIVL_MAXLOC)
			countStep = 2;

		if (concCount == null) {
			SymbolicExpression[] singleOperand0 = new SymbolicExpression[countStep];
			SymbolicExpression[] singleOperand1 = new SymbolicExpression[countStep];
			SymbolicExpression[] result = new SymbolicExpression[countStep];
			NumericExpression totalUnits = universe.multiply(count,
					universe.integer(countStep));
			NumericSymbolicConstant identifier = (NumericSymbolicConstant) universe
					.symbolicConstant(universe.stringObject("j"),
							universe.integerType());

			for (int w = 0; w < countStep; w++) {
				singleOperand0[w] = universe.arrayRead(operand0,
						universe.add(identifier, universe.integer(w)));
				singleOperand1[w] = universe.arrayRead(operand1,
						universe.add(identifier, universe.integer(w)));
			}
			result = singleApplyCIVLOperation(state, process, singleOperand0,
					singleOperand1, CIVLOp, countStep, civlsource);
			if (countStep == 1) {
				// optimization
				return universe.arrayLambda(
						universe.arrayType(elementType, totalUnits),
						universe.lambda(identifier, result[0]));
			} else {
				// When an operand contains more than one basic elements (e.g.
				// MINLOC or MAXLOC), the return the value will be constructed
				// as follows:
				// For the result of an single operation:
				// R := {a[j], b[x(j)], c[y(j)]...}, where j is a symbolic
				// constant and x(j) ,y(j) is a (integer->integer) function on
				// j.
				//
				// For the whole array w which consists of "count" Rs, given a
				// valid index i, it should return w[i].
				// w[i] := R[i - i%step]; Where R[k] := is the k-th element of R
				// with a substitution on j with k.

				// j % countStep:
				NumericExpression identOffset = universe.modulo(identifier,
						universe.integer(countStep));
				// j - j % countStep:
				NumericExpression identBase = universe.subtract(identifier,
						identOffset);
				SymbolicExpression function;

				// For R := {a[j], b[x(j)], c[y(j)]...}, giving a index k, R' is
				// computed by update all elements in R with a substitution on j
				// with k. Note here k := i - i % countStep, i is an arbitrary
				// valid index on the whole array w:
				for (int i = 0; i < countStep; i++)
					result[i] = universe.apply(
							universe.lambda(identifier, result[i]),
							Arrays.asList(identBase));
				// make R' an array:
				function = universe.array(elementType, result);
				function = universe.lambda(identifier,
						universe.arrayRead(function, identOffset));
				return universe.arrayLambda(
						universe.arrayType(elementType, totalUnits), function);
			}
		} else {
			int countInt = ((IntegerNumber) concCount).intValue();

			if (countInt <= 0)
				return universe.emptyArray(elementType);

			int totalUnits = countInt * countStep;
			SymbolicExpression[] singleOperand0 = new SymbolicExpression[countStep];
			SymbolicExpression[] singleOperand1 = new SymbolicExpression[countStep];
			SymbolicExpression[] result = new SymbolicExpression[totalUnits];
			SymbolicExpression[] singleResult;

			for (int i = 0; i < totalUnits; i = i + countStep) {
				for (int w = 0; w < countStep; w++) {
					singleOperand0[w] = universe.arrayRead(operand0,
							universe.integer(i + w));
					singleOperand1[w] = universe.arrayRead(operand1,
							universe.integer(i + w));
				}

				singleResult = singleApplyCIVLOperation(state, process,
						singleOperand0, singleOperand1, CIVLOp, countStep,
						civlsource);
				System.arraycopy(singleResult, 0, result, i, countStep);
			}
			return universe.array(elementType, result);
		}
	}

	/**
	 * Completing an operation (which is included in CIVLOperation enumerator).
	 * 
	 * @author Ziqing Luo
	 * @param arg0
	 *            The new data got from the bundle
	 * @param arg1
	 *            The data has already been received previously
	 * @param op
	 *            The CIVL Operation
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression[] singleApplyCIVLOperation(State state,
			String process, SymbolicExpression op0[], SymbolicExpression op1[],
			CIVLOperator op, int numElementsInOperand, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		SymbolicExpression[] result = new SymbolicExpression[numElementsInOperand];

		/*
		 * For MAX and MIN operation, if CIVL cannot figure out a concrete
		 * result, make a abstract function for it.
		 */
		try {
			switch (op) {
				// TODO: consider using heuristic to switch to abstract
				// functions if these expressions get too big (max,min):
				case CIVL_MAX :
					claim = universe.lessThan((NumericExpression) op1[0],
							(NumericExpression) op0[0]);
					result[0] = universe.cond(claim, op0[0], op1[0]);
					break;
				case CIVL_MIN :
					claim = universe.lessThan((NumericExpression) op0[0],
							(NumericExpression) op1[0]);
					result[0] = universe.cond(claim, op0[0], op1[0]);
					break;
				case CIVL_SUM :
					result[0] = universe.add((NumericExpression) op0[0],
							(NumericExpression) op1[0]);
					break;
				case CIVL_PROD :
					result[0] = universe.multiply((NumericExpression) op0[0],
							(NumericExpression) op1[0]);
					break;
				case CIVL_LAND :
					result[0] = universe.and((BooleanExpression) op0[0],
							(BooleanExpression) op1[0]);
					break;
				case CIVL_LOR :
					result[0] = universe.or((BooleanExpression) op0[0],
							(BooleanExpression) op1[0]);
					break;
				case CIVL_LXOR :
					BooleanExpression notNewData = universe
							.not((BooleanExpression) op0[0]);
					BooleanExpression notPrevData = universe
							.not((BooleanExpression) op1[0]);

					result[0] = universe.or(
							universe.and(notNewData,
									(BooleanExpression) op0[0]),
							universe.and((BooleanExpression) op1[0],
									notPrevData));
					break;
				case CIVL_MINLOC :
					return applyMINOrMAXLOC(state, process, op0, op1, true,
							civlsource);
				case CIVL_MAXLOC :
					return applyMINOrMAXLOC(state, process, op0, op1, false,
							civlsource);
				case CIVL_REPLACE :
				case CIVL_BAND :
				case CIVL_BOR :
				case CIVL_BXOR :
				default :
					throw new CIVLUnimplementedFeatureException(
							"CIVLOperation: " + op.name());
			}
			return result;
		} catch (ClassCastException e) {
			errorLogger.logSimpleError(civlsource, state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"Invalid operands type for CIVL Operation: " + op.name());
			throw new UnsatisfiablePathConditionException();
		}
	}

	protected CIVLOperator translateOperator(int op) {
		return CIVLOperator.values()[op];
	}

	/**
	 * <p>
	 * <b>Summary: </b> Apply MIN_LOC or MAX_LOC operation on two operands.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param operands
	 *            An array of all operands:
	 *            <code>{loc0, idx0, loc1, idx1}</code>
	 * @param isMin
	 *            A flag, true for MIN_LOC operation, false for MAX_LOC
	 *            operation.
	 * @param civlsource
	 *            {@link CIVLSource} of the operation
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression[] applyMINOrMAXLOC(State state, String process,
			SymbolicExpression[] operand0, SymbolicExpression[] operand1,
			boolean isMin, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		NumericExpression locations[] = {(NumericExpression) operand0[0],
				(NumericExpression) operand1[0]};
		NumericExpression indices[] = {(NumericExpression) operand0[1],
				(NumericExpression) operand1[1]};

		assert (operand0.length == 2) && (operand1.length == 2);
		return isMin
				? applyMinLocOperation(locations, indices)
				: applyMaxLocOperation(locations, indices);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Apply a MINLOC operation on two operands: [loc0, idx0]
	 * and [loc1, idx1]
	 * </p>
	 * 
	 * @param locations
	 *            Location array which consists of a "location0" and a
	 *            "location1"
	 * @param indices
	 *            Index array which consists of a "index0" and a "index1"
	 * @return loc0 \lt loc1 ? [loc0, idx0] : loc0 != loc1 ? [loc1, idx1] : idx0
	 *         \lt idx1 ? [loc0, idx0]: [loc1, idx1]
	 */
	private SymbolicExpression[] applyMinLocOperation(
			NumericExpression locations[], NumericExpression indices[]) {
		BooleanExpression loc0LTloc1 = universe.lessThan(locations[0],
				locations[1]);
		BooleanExpression loc0NEQloc1 = universe
				.not(universe.equals(locations[0], locations[1]));
		BooleanExpression idx0LTidx1 = universe.lessThan(indices[0],
				indices[1]);
		SymbolicExpression locResult, idxResult;

		// optimize:
		if (loc0LTloc1.isTrue() && loc0NEQloc1.isTrue()) {
			SymbolicExpression[] result = {locations[0], indices[0]};

			return result;
		} else {
			locResult = universe.cond(loc0LTloc1, locations[0], locations[1]);
			idxResult = universe.cond(loc0LTloc1, indices[0],
					universe.cond(loc0NEQloc1, indices[1],
							universe.cond(idx0LTidx1, indices[0], indices[1])));

			SymbolicExpression[] result = {locResult, idxResult};

			return result;
		}
	}

	/**
	 * <p>
	 * <b>Summary: </b> Apply a MAXLOC operation on two operands: [loc0, idx0]
	 * and [loc1, idx1]
	 * </p>
	 * 
	 * 
	 * @param locations
	 *            Location array which consists of a "location0" and a
	 *            "location1"
	 * @param indices
	 *            Index array which consists of a "index0" and a "index1"
	 * @return loc0 \gt loc1 ? [loc0, idx0] : loc0 != loc1 ? [loc1, idx1] : idx0
	 *         \lt idx1 ? [loc0, idx0]: [loc1, idx1]
	 * @return
	 */
	private SymbolicExpression[] applyMaxLocOperation(
			NumericExpression locations[], NumericExpression indices[]) {
		BooleanExpression loc0GTloc1 = universe.lessThan(locations[1],
				locations[0]);
		BooleanExpression loc0NEQloc1 = universe
				.not(universe.equals(locations[0], locations[1]));
		BooleanExpression idx0LTidx1 = universe.lessThan(indices[0],
				indices[1]);
		SymbolicExpression locResult, idxResult;

		// optimize:
		if (loc0GTloc1.isTrue() && loc0NEQloc1.isTrue()) {
			SymbolicExpression[] result = {locations[0], indices[0]};

			return result;
		} else {
			locResult = universe.cond(loc0GTloc1, locations[0], locations[1]);
			idxResult = universe.cond(loc0GTloc1, indices[0],
					universe.cond(loc0NEQloc1, indices[1],
							universe.cond(idx0LTidx1, indices[0], indices[1])));

			SymbolicExpression[] result = {locResult, idxResult};

			return result;

		}
	}

	protected Pair<State, SymbolicExpression[]> evaluateArguments(State state,
			int pid, Expression[] arguments)
			throws UnsatisfiablePathConditionException {
		int numArgs = arguments.length;
		SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];

		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			eval = symbolicAnalyzer.evaluator().evaluate(state, pid,
					arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		return new Pair<>(state, argumentValues);

	}

	/**
	 * Pre-conditions:
	 * <ol>
	 * <li>"pointer" is a valid pointer</li>
	 * <li>"count" greater than zero</li>
	 * <li>"dataArray" is an one dimensional array</li>
	 * <li>"pointer" must points to a compatible type with the "dataArray"</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
	 * Setting a sequence of data starting from a pointer
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param pointer
	 *            The pointer to the start position
	 * @param count
	 *            The number of cells in the array of data
	 * @param dataArray
	 *            The sequence of data is going to be set
	 * @param checkOutput
	 *            Flag for check output variable
	 * @param source
	 *            CIVL source of the statement
	 * @return A pair of evaluation and pointer.The data in form of an array
	 *         which can be assigned to the returned pointer.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Pair<Evaluation, SymbolicExpression> setDataFrom(State state,
			int pid, String process, Expression ptrExpr,
			SymbolicExpression pointer, NumericExpression count,
			SymbolicExpression dataArray, boolean checkOutput,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		NumericExpression[] arraySlicesSizes;
		NumericExpression startPos;
		NumericExpression dataSeqLength = universe.length(dataArray);
		SymbolicExpression startPtr, endPtr;
		Evaluation eval;
		Pair<Evaluation, NumericExpression[]> eval_and_slices;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ReferenceExpression symref;
		BooleanExpression claim;
		ResultType resultType;
		int dim;

		// If data length > count, report an error:
		if (!this.civlConfig.svcomp()) {
			claim = universe.lessThan(dataSeqLength, count);
			resultType = reasoner.valid(claim).getResultType();
			if (resultType.equals(ResultType.YES))
				reportOutOfBoundError(state, process, claim, resultType,
						pointer, dataSeqLength, count, source);
		}
		// If count is one:
		if (reasoner.isValid(universe.equals(count, one))) {
			SymbolicExpression data = universe.arrayRead(dataArray, zero);

			return new Pair<>(new Evaluation(state, data), pointer);
		}
		// If the type of the object is exact same as the dataArray, then do a
		// directly assignment:
		CIVLType typeObj = symbolicAnalyzer
				.typeOfObjByPointer(ptrExpr.getSource(), state, pointer);
		TypeEvaluation teval = evaluator.getDynamicType(state, pid, typeObj,
				source, false);

		state = teval.state;
		if (dataArray.type().equals(teval.type))
			return new Pair<>(new Evaluation(state, dataArray), pointer);

		// Else, count greater than one:
		startPtr = pointer;
		eval_and_slices = evaluator.evaluatePointerAdd(state, process, startPtr,
				count, checkOutput, source);
		eval = eval_and_slices.left;
		endPtr = eval.value;
		state = eval.state;
		arraySlicesSizes = eval_and_slices.right;
		// If the pointer addition happens to be done within one dimensional
		// space, the "arraySlicesSizes" is null and we don't really need it.
		if (arraySlicesSizes == null) {
			arraySlicesSizes = new NumericExpression[1];
			arraySlicesSizes[0] = one;
		}
		dim = arraySlicesSizes.length;
		// "startPtr" may not point to a memory base type object yet
		symref = symbolicAnalyzer.getMemBaseReference(state, startPtr, source);
		startPtr = symbolicUtil.makePointer(startPtr, symref);
		startPos = zero;
		if (symref.isArrayElementReference()) {
			NumericExpression[] startIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symref);
			int numIndices = startIndices.length;

			for (int i = 1; !startPtr.equals(endPtr); i++) {
				startPtr = symbolicUtil.parentPointer(source, startPtr);
				endPtr = symbolicUtil.parentPointer((CIVLSource) null, endPtr);
				startPos = universe.add(startPos,
						universe.multiply(startIndices[numIndices - i],
								arraySlicesSizes[dim - i]));
			}
		}
		// here "startPtr" is already updated as the pointer to the common sub
		// array.
		eval = evaluator.dereference(source, state, process, ptrExpr, startPtr,
				false);
		state = eval.state;
		if (eval.value.type().typeKind().equals(SymbolicTypeKind.ARRAY)) {
			eval = this.setDataBetween(state, process, eval.value,
					arraySlicesSizes, startPos, count, pointer, dataArray,
					source);
		} else {
			reportOutOfBoundError(state, process, null, null, startPtr, one,
					count, source);
		}
		return new Pair<>(eval, startPtr);
	}

	/**
	 * Pre-condition:
	 * <ol>
	 * <li>"pointer" is valid</li>
	 * <li>"count" >= 0</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
	 * Get a sequence of data starting from a pointer.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param pointer
	 *            The pointer to the start position of a sequence of data
	 * @param count
	 *            The number of cells in the array of data
	 * @param checkOutput
	 *            Flag for check output variable
	 * @param source
	 *            CIVL source of the statement
	 * @return Evaluation contains the sequence of data which is in form of a
	 *         one dimensional array.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation getDataFrom(State state, int pid, String process,
			Expression pointerExpr, SymbolicExpression pointer,
			NumericExpression count, boolean toBase, boolean checkOutput,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		NumericExpression[] arraySlicesSizes;
		NumericExpression startPos;
		SymbolicExpression startPtr, endPtr;
		SymbolicExpression commonArray;
		ReferenceExpression symref;
		Evaluation eval;
		int dim;
		Pair<Evaluation, NumericExpression[]> pointer_and_slices;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		CIVLPointerType ptrType = (CIVLPointerType) pointerExpr
				.getExpressionType();
		CIVLType referencedType = ptrType.baseType();
		TypeEvaluation teval = evaluator.getDynamicType(state, pid,
				referencedType, source, true);

		state = teval.state;
		// If "count" == 0:
		if (reasoner.isValid(universe.equals(count, zero))) {
			SymbolicExpression result = universe.emptyArray(teval.type);

			return new Evaluation(state, result);
		}
		// If "count" == 1:
		if (reasoner.isValid(universe.equals(count, one))) {
			eval = evaluator.dereference(source, state, process, pointerExpr,
					pointer, true);
			eval.value = universe.array(eval.value.type(),
					Arrays.asList(eval.value));
			eval.value = arrayFlatten(state, process, eval.value, source);
			return eval;
		}
		// Else "count" > 1 :
		startPtr = pointer;
		pointer_and_slices = evaluator.evaluatePointerAdd(state, process,
				startPtr, count, false, source);
		arraySlicesSizes = pointer_and_slices.right;
		eval = pointer_and_slices.left;
		endPtr = eval.value;
		// If the pointer addition happens to be done within one dimensional
		// space, the "arraySlicesSizes" is null and we don't really need it.
		if (arraySlicesSizes == null) {
			arraySlicesSizes = new NumericExpression[1];
			arraySlicesSizes[0] = one;
		}
		// startPtr may not be the memory base type reference form yet
		if (toBase) {
			symref = symbolicAnalyzer.getMemBaseReference(state, startPtr,
					source);
			startPtr = symbolicUtil.makePointer(startPtr, symref);
		} else
			symref = symbolicUtil.getSymRef(startPtr);
		startPos = zero;
		if (symref.isArrayElementReference()) {
			NumericExpression[] startPtrIndices = symbolicUtil
					.stripIndicesFromReference((ArrayElementReference) symref);
			int numIndices = startPtrIndices.length;

			dim = arraySlicesSizes.length;
			for (int i = 1; !startPtr.equals(endPtr); i++) {
				startPtr = symbolicUtil.parentPointer(source, startPtr);
				endPtr = symbolicUtil.parentPointer((CIVLSource) null, endPtr);
				startPos = universe.add(startPos,
						universe.multiply(startPtrIndices[numIndices - i],
								arraySlicesSizes[dim - i]));
			}
		}
		eval = evaluator.dereference(source, state, process, pointerExpr,
				startPtr, true);
		state = eval.state;
		commonArray = eval.value;
		if (commonArray.type().typeKind() == SymbolicTypeKind.ARRAY)
			eval.value = getDataBetween(state, process, startPos, count,
					commonArray, arraySlicesSizes, source);
		else
			reportOutOfBoundError(state, process, null, null, startPtr, one,
					count, source);
		return eval;
	}

	/**
	 * Cast an array to another array. The two arrays before and after casting
	 * must be able to hold same number of non-array elements.<br>
	 * e.g. For arrays <code>int a[2][2]; int b[4]; int c[5]</code>, a and b can
	 * be casted into each other but both of them can not be casted to c.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param oldArray
	 *            The array before casting
	 * @param targetTypeArray
	 *            The array has the type which is the target type of casting
	 * @param source
	 *            The CIVL source of the oldArray or the pointer to OldArray
	 * @return casted array
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression arrayCasting(State state, String process,
			SymbolicExpression oldArray, SymbolicCompleteArrayType typeTemplate,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		NumericExpression[] coordinatesSizes, arraySlicesSizes;
		// temporary arrays store dimensional slices
		SymbolicExpression[] arraySlices;
		SymbolicExpression flattenOldArray;
		ResultType resultType;
		IntegerNumber flattenLength;
		IntegerNumber dimensionalSpace;
		SymbolicType elementType;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int dim, numElements;

		assert (typeTemplate.typeKind().equals(SymbolicTypeKind.ARRAY));
		assert typeTemplate.isComplete() : "arrayCasting internal exception";
		if (oldArray.type().equals(typeTemplate))
			return oldArray;
		flattenOldArray = arrayFlatten(state, process, oldArray, source);
		flattenLength = (IntegerNumber) reasoner
				.extractNumber(universe.length(flattenOldArray));
		if (flattenLength == null)
			throw new CIVLUnimplementedFeatureException(
					"Transform arrays with non-concrete sizes");
		arraySlices = new SymbolicExpression[flattenLength.intValue()];
		coordinatesSizes = symbolicUtil.arrayCoordinateSizes(typeTemplate);
		arraySlicesSizes = symbolicUtil.arraySlicesSizes(coordinatesSizes);
		elementType = ((SymbolicArrayType) flattenOldArray.type())
				.elementType();
		if (!this.civlConfig.svcomp()) {
			// check if the flatten array is compatible with the given array
			// type
			claim = universe.equals(universe.length(flattenOldArray), universe
					.multiply(arraySlicesSizes[0], coordinatesSizes[0]));
			resultType = reasoner.valid(claim).getResultType();
			if (!resultType.equals(ResultType.YES))
				throw new CIVLInternalException(
						"Casting an array between incompatiable types", source);
		}
		dim = coordinatesSizes.length;
		// Extracting sub-arrays out of SYMBOLIC flatten array
		dimensionalSpace = (IntegerNumber) reasoner
				.extractNumber(coordinatesSizes[dim - 1]);
		if (dimensionalSpace == null)
			throw new CIVLUnimplementedFeatureException(
					"Transform arrays with non-concrete sizes");
		numElements = flattenLength.intValue();
		for (int j = 0, i = 0; j < flattenLength
				.intValue(); j += dimensionalSpace.intValue()) {
			arraySlices[i++] = symbolicAnalyzer
					.getSubArray(flattenOldArray, universe.integer(j),
							universe.add(universe.integer(j),
									coordinatesSizes[dim - 1]),
							state, process, source);
		}
		numElements /= dimensionalSpace.intValue();
		elementType = universe.arrayType(elementType,
				coordinatesSizes[dim - 1]);
		// Keep compressing sub-arrays
		for (int i = dim - 1; --i >= 0;) {
			SymbolicExpression[] subArray;

			dimensionalSpace = (IntegerNumber) reasoner
					.extractNumber(coordinatesSizes[i]);
			if (dimensionalSpace == null)
				throw new CIVLUnimplementedFeatureException(
						"Transform arrays with non-concrete sizes");
			numElements /= dimensionalSpace.intValue();
			for (int j = 0; j < numElements; j++) {
				int offset = j * dimensionalSpace.intValue();

				subArray = Arrays.copyOfRange(arraySlices, offset,
						offset + dimensionalSpace.intValue());
				arraySlices[j] = universe.array(elementType,
						Arrays.asList(subArray));
			}
			elementType = universe.arrayType(elementType, coordinatesSizes[i]);
		}
		return arraySlices[0];
	}

	/**
	 * Flatten the given array. Here flatten means converting a nested array
	 * (which represents multiple dimensional array in CIVL) to an one
	 * dimensional array.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param array
	 *            The array which is going to be flatten
	 * @param civlsource
	 *            The CIVL source the array or the pointer to the array
	 * @return the flatten array
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression arrayFlatten(State state, String process,
			SymbolicExpression array, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		List<SymbolicExpression> flattenElementList;
		NumericExpression[] arrayElementsSizes;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		if (array == null)
			throw new CIVLInternalException("parameter 'array' is null.",
					civlsource);
		if (array.isNull())
			return array;
		// If the array is already a one-dimensional array no matter if the
		// length is concrete or non-concrete, return it directly.
		if (!(((SymbolicArrayType) array.type())
				.elementType() instanceof SymbolicArrayType))
			return array;
		// If the array has at least one dimension whose length is non-concrete,
		// using array lambda to flatten it.
		if (this.hasNonConcreteExtent(reasoner, array)) {
			if (array.type().typeKind().equals(SymbolicTypeKind.ARRAY))
				arrayElementsSizes = symbolicUtil
						.arraySlicesSizes(symbolicUtil.arrayCoordinateSizes(
								(SymbolicCompleteArrayType) array.type()));
			else {
				arrayElementsSizes = new NumericExpression[1];
				arrayElementsSizes[0] = one;
			}
			return this.arrayLambdaFlatten(state, array, arrayElementsSizes,
					civlsource);
		}
		flattenElementList = this.arrayFlattenWorker(state, array, civlsource);
		if (flattenElementList.size() > 0) {
			assert (!(flattenElementList.get(0)
					.type() instanceof SymbolicArrayType));
			return universe.array(flattenElementList.get(0).type(),
					flattenElementList);
		} else if (array instanceof SymbolicArrayType)
			return universe
					.emptyArray(((SymbolicArrayType) array).elementType());
		else
			return universe.emptyArray(array.type());
	}

	/**
	 * Pre-condition:
	 * <ol>
	 * <li>"pointer" points to the start position</li>
	 * <li>"count" > 0</li>
	 * <li>"count" >= length(dataSequence)</li>
	 * <li>"array" has {@link SymbolicCompleteArrayType}</li>
	 * <li>"dataSequence" is an one dimensional array</li>
	 * </ol>
	 * Post-condition:
	 * <ol>
	 * <li>left side of the pair: Return the new value of the pointed object
	 * after assigning the given data sequence from pointed position</li>
	 * <li>right side of the pair: Return the pointer which can be assigned with
	 * the new value</li>
	 * </ol>
	 * Setting a sequence of data between two array element references. Returns
	 * the settled new array and the pointer to that array.
	 * 
	 * Pre-condition: start pointer and end pointer should point to the same
	 * object.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param startPtr
	 *            The pointer to the start position
	 * @param endPtr
	 *            The pointer to the end position
	 * @param dataSequence
	 *            The sequence of data which is going to be set
	 * @param arraySlicesSizes
	 *            The capacity information of the array pointed by the startPtr
	 *            or endPtr(These two pointers point to the same object).<br>
	 *            Note: Here capacity information of an array means that for one
	 *            cell in each dimension of an array how many non-array elements
	 *            it can hold. e.g. For array <code>int a[2][2];</code>, the one
	 *            cell in deepest dimension can only hold one element while one
	 *            cell in the second deepest dimension can hold 2 elements. Here
	 *            we use 0 marking (which is key in the given map) the deepest
	 *            dimension and 1 marking the second deepest dimension and so
	 *            forth.
	 * @param source
	 *            The CIVL source of the start pointer.
	 * @return the settled new array and the pointer to that array.
	 * @throws UnsatisfiablePathConditionException
	 * @author Ziqing Luo
	 */
	private Evaluation setDataBetween(State state, String process,
			SymbolicExpression array, NumericExpression[] arraySlicesSizes,
			NumericExpression startPos, NumericExpression count,
			SymbolicExpression pointer, SymbolicExpression dataSequence,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression flattenArray;
		NumericExpression dataSize;
		NumericExpression i, j;
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		dataSize = universe.length(dataSequence);
		// Direct assignment conditions:
		// 1. start position is zero.
		// 2. Interval between pointers equals to data size.
		// 3. The least common array capacity equals to data size.
		if (reasoner.isValid(universe.equals(startPos, zero))
				&& arraySlicesSizes.length == 1) {
			NumericExpression arraySize = universe.length(array);

			claim = universe.and(universe.equals(dataSize, count),
					universe.equals(dataSize, arraySize));
			if (reasoner.isValid(claim))
				return new Evaluation(state, dataSequence);
		} // TODO: what if the length of dataSize is non-concrete and cannot be
			// decided by reasoner?
		flattenArray = arrayFlatten(state, process, array, source);
		i = startPos;
		j = zero;
		claim = universe.lessThan(j, dataSize);
		while (reasoner.isValid(claim)) {
			SymbolicExpression elementInDataArray = null;

			elementInDataArray = universe.arrayRead(dataSequence, j);
			flattenArray = universe.arrayWrite(flattenArray, i,
					elementInDataArray);
			i = universe.add(i, one);
			j = universe.add(j, one);
			claim = universe.lessThan(j, dataSize);
		}
		flattenArray = arrayCasting(state, process, flattenArray,
				(SymbolicCompleteArrayType) array.type(), source);
		return new Evaluation(state, flattenArray);
	}

	/**
	 * pre-condition:
	 * <ol>
	 * <li>endPos - startPos > 0</li>
	 * <li>array has {@link SymbolicCompleteArrayType}</li>
	 * <li>arraySlicesSize[0] >= endPos - startPos</li>
	 * </ol>
	 * post_condition:
	 * <ol>
	 * <li>Return a sequence of data with length "count" from the pointed object
	 * starting from the pointed position</li>
	 * </ol>
	 * Get sequence of data between two array element references. Returns the
	 * sequence of data which is in form of an one dimensional array.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param startPtr
	 *            The pointer to the start position
	 * @param endPtr
	 *            The pointer to the end position
	 * @param arrayElementsSizes
	 *            same as the same argument in {@link #setDataBetween(State,
	 *            String, SymbolicExpression, SymbolicExpression,
	 *            SymbolicExpression, Map<Integer, NumericExpression>,
	 *            CIVLSource)}
	 * @param source
	 *            The CIVL source of start pointer.
	 * @return a sequence of data which is in form of an one dimensional array.
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression getDataBetween(State state, String process,
			NumericExpression startPos, NumericExpression count,
			SymbolicExpression array, NumericExpression[] arraySlicesSizes,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression flattenArray;

		// TODO: getSubArray not support non-concrete length
		flattenArray = arrayFlatten(state, process, array, source);
		return symbolicAnalyzer.getSubArray(flattenArray, startPos,
				universe.add(startPos, count), state, process, source);
	}

	/**
	 * Recursively flatten the given array. Only can be used on arrays have
	 * concrete lengths.
	 */
	private List<SymbolicExpression> arrayFlattenWorker(State state,
			SymbolicExpression array, CIVLSource civlsource) {
		BooleanExpression pathCondition = state.getPathCondition();
		List<SymbolicExpression> flattenElementList = new LinkedList<>();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (array.isNull() || array == null)
			throw new CIVLInternalException("parameter array is null.",
					civlsource);

		if (array.type() instanceof SymbolicArrayType) {
			BooleanExpression claim;
			NumericExpression i = universe.zeroInt();
			NumericExpression length = universe.length(array);

			claim = universe.lessThan(i, length);
			if (((SymbolicArrayType) array.type())
					.elementType() instanceof SymbolicArrayType) {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					flattenElementList.addAll(
							arrayFlattenWorker(state, element, civlsource));
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			} else {
				while (reasoner.isValid(claim)) {
					SymbolicExpression element = universe.arrayRead(array, i);

					flattenElementList.add(element);
					// update
					i = universe.add(i, one);
					claim = universe.lessThan(i, length);
				}
			}
		} else {
			flattenElementList.add(array);
		}
		return flattenElementList;
	}

	/**
	 * Helper function for
	 * {@link #arrayFlatten(State, String, SymbolicExpression, CIVLSource)}.
	 * Used for dealing with arrays have non-concrete lengths.
	 */
	private SymbolicExpression arrayLambdaFlatten(State state,
			SymbolicExpression array, NumericExpression[] arrayElementsSizes,
			CIVLSource civlsource) {
		// Temporary array object during processing
		SymbolicExpression tempArray = array;
		NumericSymbolicConstant index = null;
		SymbolicType elementType = null;
		SymbolicExpression arrayEleFunc = null;
		SymbolicExpression lambdaFunc;
		SymbolicExpression newArray = null;
		SymbolicCompleteArrayType newArrayType;
		int dim;
		NumericExpression capacity = one;
		NumericExpression tempIndex;
		NumericExpression newExtent;

		index = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("i"), universe.integerType());
		// From outer to inner. later from inner to outer
		dim = arrayElementsSizes.length;
		tempIndex = index;
		newExtent = one;
		for (int i = 0; i < dim; i++) {
			NumericExpression newIndex; // new index is remainder

			capacity = arrayElementsSizes[i];
			newIndex = universe.divide(tempIndex, capacity);
			newExtent = universe.multiply(newExtent,
					universe.length(tempArray));
			tempArray = universe.arrayRead(tempArray, newIndex);
			tempIndex = universe.modulo(tempIndex, capacity);
		}
		elementType = tempArray.type();
		arrayEleFunc = universe.canonic(tempArray);
		lambdaFunc = universe.lambda(index, arrayEleFunc);
		newArrayType = universe.arrayType(elementType, newExtent);
		newArray = universe.arrayLambda(newArrayType, lambdaFunc);
		assert (newArray != null);
		return newArray;
	}

	/**
	 * Helper function for
	 * {@link #arrayFlatten(State , String, SymbolicExpression , CIVLSource)}.
	 * Returns true if and only if there is at least one array (in nested arrays
	 * ) has non-concrete length.
	 */
	private boolean hasNonConcreteExtent(Reasoner reasoner,
			SymbolicExpression array) {
		NumericExpression extent;
		SymbolicExpression element = array;
		SymbolicType type = array.type();

		while (type instanceof SymbolicArrayType) {
			extent = universe.length(element);
			if (reasoner.extractNumber(extent) == null)
				return true;
			element = universe.arrayRead(element, zero);
			type = element.type();
		}
		return false;
	}

	/**
	 * Helper function of report an out of bound error.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The string identifier of the process
	 * @param claim
	 *            The {@link BooleanExpression} of the predicate (optional, can
	 *            be null)
	 * @param resultType
	 *            The {@link ResultType} of reasoning the predicate (optional,
	 *            can be null)
	 * @param pointer
	 *            The pointer to the array
	 * @param arrayLength
	 *            The length of the array
	 * @param offset
	 *            The offset of the element from the position pointed by pointer
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private void reportOutOfBoundError(State state, String process,
			BooleanExpression claim, ResultType resultType,
			SymbolicExpression pointer, NumericExpression arrayLength,
			NumericExpression offset, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		String message = "Out of bound error may happen when access on an array element.\n"
				+ "Pointer:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						null, pointer)
				+ "\n" + "Offset:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						null, offset)
				+ "\n" + "Array length:"
				+ symbolicAnalyzer.symbolicExpressionToString(source, state,
						null, arrayLength);

		if (claim != null && resultType != null)
			state = errorLogger.logError(source, state, process,
					symbolicAnalyzer.stateInformation(state), claim, resultType,
					ErrorKind.OUT_OF_BOUNDS, message);
		else
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.OUT_OF_BOUNDS, message);
		throw new UnsatisfiablePathConditionException();
	}

}
