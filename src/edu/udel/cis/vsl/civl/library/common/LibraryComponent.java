package edu.udel.cis.vsl.civl.library.common;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

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

	// protected boolean statelessPrintf;

	protected CIVLTypeFactory typeFactory;

	/**
	 * The CIVL configuration object
	 */
	protected CIVLConfiguration civlConfig;

	protected CIVLErrorLogger errorLogger;

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
	protected LibraryComponent(String name, SymbolicUniverse universe, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig, LibraryEvaluatorLoader libEvaluatorLoader,
			ModelFactory modelFactory, CIVLErrorLogger errLogger) {
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
	protected SymbolicExpression applyCIVLOperation(State state, int pid, String process, SymbolicExpression operands[],
			CIVLOperator CIVLOp, NumericExpression count, SymbolicType elementType, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		Number concCount = reasoner.extractNumber(count);
		SymbolicExpression operand0 = operands[0];
		SymbolicExpression operand1 = operands[1];
		int countStep = 1;

		if (CIVLOp == CIVLOperator.CIVL_MINLOC || CIVLOp == CIVLOperator.CIVL_MAXLOC)
			countStep = 2;

		if (concCount == null) {
			SymbolicExpression[] singleOperand0 = new SymbolicExpression[countStep];
			SymbolicExpression[] singleOperand1 = new SymbolicExpression[countStep];
			SymbolicExpression[] result = new SymbolicExpression[countStep];
			NumericExpression totalUnits = universe.multiply(count, universe.integer(countStep));
			NumericSymbolicConstant identifier = (NumericSymbolicConstant) universe
					.symbolicConstant(universe.stringObject("j"), universe.integerType());

			for (int w = 0; w < countStep; w++) {
				singleOperand0[w] = universe.arrayRead(operand0, universe.add(identifier, universe.integer(w)));
				singleOperand1[w] = universe.arrayRead(operand1, universe.add(identifier, universe.integer(w)));
			}
			result = singleApplyCIVLOperation(state, process, singleOperand0, singleOperand1, CIVLOp, countStep,
					civlsource);
			if (countStep == 1) {
				// optimization
				return universe.arrayLambda(universe.arrayType(elementType, totalUnits),
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
				NumericExpression identOffset = universe.modulo(identifier, universe.integer(countStep));
				// j - j % countStep:
				NumericExpression identBase = universe.subtract(identifier, identOffset);
				SymbolicExpression function;

				// For R := {a[j], b[x(j)], c[y(j)]...}, giving a index k, R' is
				// computed by update all elements in R with a substitution on j
				// with k. Note here k := i - i % countStep, i is an arbitrary
				// valid index on the whole array w:
				for (int i = 0; i < countStep; i++)
					result[i] = universe.apply(universe.lambda(identifier, result[i]), Arrays.asList(identBase));
				// make R' an array:
				function = universe.array(elementType, result);
				function = universe.lambda(identifier, universe.arrayRead(function, identOffset));
				return universe.arrayLambda(universe.arrayType(elementType, totalUnits), function);
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
					singleOperand0[w] = universe.arrayRead(operand0, universe.integer(i + w));
					singleOperand1[w] = universe.arrayRead(operand1, universe.integer(i + w));
				}

				singleResult = singleApplyCIVLOperation(state, process, singleOperand0, singleOperand1, CIVLOp,
						countStep, civlsource);
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
	private SymbolicExpression[] singleApplyCIVLOperation(State state, String process, SymbolicExpression op0[],
			SymbolicExpression op1[], CIVLOperator op, int numElementsInOperand, CIVLSource civlsource)
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
			case CIVL_MAX:
				claim = universe.lessThan((NumericExpression) op1[0], (NumericExpression) op0[0]);
				result[0] = universe.cond(claim, op0[0], op1[0]);
				break;
			case CIVL_MIN:
				claim = universe.lessThan((NumericExpression) op0[0], (NumericExpression) op1[0]);
				result[0] = universe.cond(claim, op0[0], op1[0]);
				break;
			case CIVL_SUM:
				result[0] = universe.add((NumericExpression) op0[0], (NumericExpression) op1[0]);
				break;
			case CIVL_PROD:
				result[0] = universe.multiply((NumericExpression) op0[0], (NumericExpression) op1[0]);
				break;
			case CIVL_LAND:
				result[0] = universe.and((BooleanExpression) op0[0], (BooleanExpression) op1[0]);
				break;
			case CIVL_LOR:
				result[0] = universe.or((BooleanExpression) op0[0], (BooleanExpression) op1[0]);
				break;
			case CIVL_LXOR:
				BooleanExpression notNewData = universe.not((BooleanExpression) op0[0]);
				BooleanExpression notPrevData = universe.not((BooleanExpression) op1[0]);

				result[0] = universe.or(universe.and(notNewData, (BooleanExpression) op0[0]),
						universe.and((BooleanExpression) op1[0], notPrevData));
				break;
			case CIVL_MINLOC:
				return applyMINOrMAXLOC(state, process, op0, op1, true, civlsource);
			case CIVL_MAXLOC:
				return applyMINOrMAXLOC(state, process, op0, op1, false, civlsource);
			case CIVL_REPLACE:
			case CIVL_BAND:
			case CIVL_BOR:
			case CIVL_BXOR:
			default:
				throw new CIVLUnimplementedFeatureException("CIVLOperation: " + op.name());
			}
			return result;
		} catch (ClassCastException e) {
			errorLogger.logSimpleError(civlsource, state, process, symbolicAnalyzer.stateToString(state),
					ErrorKind.OTHER, "Invalid operands type for CIVL Operation: " + op.name());
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
	private SymbolicExpression[] applyMINOrMAXLOC(State state, String process, SymbolicExpression[] operand0,
			SymbolicExpression[] operand1, boolean isMin, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		NumericExpression locations[] = { (NumericExpression) operand0[0], (NumericExpression) operand1[0] };
		NumericExpression indices[] = { (NumericExpression) operand0[1], (NumericExpression) operand1[1] };

		assert (operand0.length == 2) && (operand1.length == 2);
		return isMin ? applyMinLocOperation(locations, indices) : applyMaxLocOperation(locations, indices);
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
	private SymbolicExpression[] applyMinLocOperation(NumericExpression locations[], NumericExpression indices[]) {
		BooleanExpression loc0LTloc1 = universe.lessThan(locations[0], locations[1]);
		BooleanExpression loc0NEQloc1 = universe.not(universe.equals(locations[0], locations[1]));
		BooleanExpression idx0LTidx1 = universe.lessThan(indices[0], indices[1]);
		SymbolicExpression locResult, idxResult;

		// optimize:
		if (loc0LTloc1.isTrue() && loc0NEQloc1.isTrue()) {
			SymbolicExpression[] result = { locations[0], indices[0] };

			return result;
		} else {
			locResult = universe.cond(loc0LTloc1, locations[0], locations[1]);
			idxResult = universe.cond(loc0LTloc1, indices[0],
					universe.cond(loc0NEQloc1, indices[1], universe.cond(idx0LTidx1, indices[0], indices[1])));

			SymbolicExpression[] result = { locResult, idxResult };

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
	private SymbolicExpression[] applyMaxLocOperation(NumericExpression locations[], NumericExpression indices[]) {
		BooleanExpression loc0GTloc1 = universe.lessThan(locations[1], locations[0]);
		BooleanExpression loc0NEQloc1 = universe.not(universe.equals(locations[0], locations[1]));
		BooleanExpression idx0LTidx1 = universe.lessThan(indices[0], indices[1]);
		SymbolicExpression locResult, idxResult;

		// optimize:
		if (loc0GTloc1.isTrue() && loc0NEQloc1.isTrue()) {
			SymbolicExpression[] result = { locations[0], indices[0] };

			return result;
		} else {
			locResult = universe.cond(loc0GTloc1, locations[0], locations[1]);
			idxResult = universe.cond(loc0GTloc1, indices[0],
					universe.cond(loc0NEQloc1, indices[1], universe.cond(idx0LTidx1, indices[0], indices[1])));

			SymbolicExpression[] result = { locResult, idxResult };

			return result;

		}
	}

	protected Pair<State, SymbolicExpression[]> evaluateArguments(State state, int pid, Expression[] arguments)
			throws UnsatisfiablePathConditionException {
		int numArgs = arguments.length;
		SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];

		for (int i = 0; i < numArgs; i++) {
			Evaluation eval = null;

			eval = symbolicAnalyzer.evaluator().evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		return new Pair<>(state, argumentValues);

	}

}
