package edu.udel.cis.vsl.civl.library.common;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * This class provides the common data and operations of library executors.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class BaseLibraryExecutor extends LibraryComponent implements
		LibraryExecutor {

	/* ************************** Protected Types ************************** */

	/* ************************** Instance Fields ************************** */

	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The primary executor of the system.
	 */
	protected Executor primaryExecutor;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	// /**
	// * The static model of the program.
	// */
	// protected Model model;

	// protected boolean statelessPrintf;

	protected CIVLErrorLogger errorLogger;

	protected CIVLConfiguration civlConfig;

	/**
	 * The set of characters that are used to construct a number in a format
	 * string.
	 */
	protected Set<Character> numbers;

	protected LibraryExecutorLoader libExecutorLoader;

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of a library executor.
	 * 
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param enablePrintf
	 *            If printing is enabled for the printf function.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility used in the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 */
	public BaseLibraryExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor.evaluator().universe(), symbolicUtil,
				symbolicAnalyzer, libEvaluatorLoader, modelFactory);
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		this.stateFactory = evaluator.stateFactory();
		this.errorLogger = primaryExecutor.errorLogger();
		this.libExecutorLoader = libExecutorLoader;
		this.civlConfig = civlConfig;
		numbers = new HashSet<Character>(10);
		for (int i = 0; i < 10; i++) {
			numbers.add(Character.forDigit(i, 10));
		}
	}

	/* ************************* Protected Methods ************************* */

	protected State executeAssert(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		BooleanExpression assertValue = (BooleanExpression) argumentValues[0];
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		reasoner = universe.reasoner(state.getPathCondition());
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();
		state = this.reportAssertionFailure(state, pid, process, resultType,
				arguments, argumentValues, source, statement, assertValue, 1);
		return state;
	}

	/**
	 * Executes the function call "$free(*void)": removes from the heap the
	 * object referred to by the given pointer.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State executeFree(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression firstElementPointer = argumentValues[0];

		if (firstElementPointer.operator() != SymbolicOperator.CONCRETE) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.UNDEFINED_VALUE, Certainty.PROVEABLE, process,
					"Attempt to free an unitialized pointer",
					symbolicAnalyzer.stateToString(state), source);

			this.errorLogger.reportError(err);
			throw new UnsatisfiablePathConditionException();
		} else if (symbolicUtil.isUndefinedPointer(firstElementPointer)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.MEMORY_LEAK, Certainty.PROVEABLE, process,
					"Attempt to free a memory space that is already freed",
					symbolicAnalyzer.stateToString(state), source);

			this.errorLogger.reportError(err);
			throw new UnsatisfiablePathConditionException();
		} else if (this.symbolicUtil.isNullPointer(firstElementPointer))
			// does nothing for null pointer.
			return state;
		else if (!this.symbolicUtil.isHeapPointer(firstElementPointer)
				|| !this.symbolicUtil.isMallocPointer(source,
						firstElementPointer)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.MEMORY_LEAK, Certainty.PROVEABLE, process,
					"The argument of free "
							+ symbolicAnalyzer.symbolicExpressionToString(
									source, state, firstElementPointer)
							+ " is not a pointer returned by a memory "
							+ "management method",
					symbolicAnalyzer.stateToString(state), source);

			this.errorLogger.reportError(err);
			throw new UnsatisfiablePathConditionException();
		} else {
			Pair<Integer, Integer> indexes;

			indexes = getMallocIndex(firstElementPointer);
			state = stateFactory
					.deallocate(state, firstElementPointer, modelFactory
							.getScopeId(source, universe.tupleRead(
									firstElementPointer, zeroObject)),
							indexes.left, indexes.right);
			return state;
		}
	}

	/**
	 * A helper function for reporting runtime assertion failure. The helper
	 * function is aiming to be re-used by both execution implementations of
	 * $assert() and $assert_equal();
	 * 
	 * @author ziqing luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The string identifier of the process
	 * @param resultType
	 *            The {@link ResultType} of the failure assertion
	 * @param arguments
	 *            The expressions of the arguments
	 * @param argumentValues
	 *            The symbolic expressions of the arguments
	 * @param source
	 *            The CIVL source of the assertion statement
	 * @param statement
	 *            The model of the statement expression
	 * @param assertValue
	 *            The boolean expression of the value of the assertion claim
	 * @param msgOffset
	 *            the start index in arguments list of the assertion failure
	 *            messages.
	 * @return the new state after reporting the assertion failure
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State reportAssertionFailure(State state, int pid,
			String process, ResultType resultType, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			CallOrSpawnStatement statement, BooleanExpression assertValue,
			int msgOffset) throws UnsatisfiablePathConditionException {
		if (resultType != ResultType.YES) {
			if (arguments.length > msgOffset) {
//				if (civlConfig.enablePrintf()) {
					Expression[] pArguments = Arrays.copyOfRange(arguments,
							msgOffset, arguments.length);
					SymbolicExpression[] pArgumentValues = Arrays.copyOfRange(
							argumentValues, msgOffset, argumentValues.length);

					state = this.primaryExecutor.execute_printf(source, state,
							pid, process, null, pArguments, pArgumentValues);
					civlConfig.out().println();
//				}
			}
			
			StringBuilder message=new StringBuilder();
			
			message.append("Assertion voilated: ");
			message.append(statement.toString());
			message.append("\nEvaluation: ");
			message.append("BLAHBLAh...");
			
			state = errorLogger.logError(source, state, process,
					symbolicAnalyzer.stateToString(state), assertValue,
					resultType, ErrorKind.ASSERTION_VIOLATION,
					"Cannot prove assertion holds: " + statement.toString()
							+ "\n  Path condition: " + state.getPathCondition()
							+ "\n  Assertion: " + assertValue + "\n");
		}
		return state;
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Obtains the field ID in the heap type via a heap-object pointer.
	 * 
	 * @param pointer
	 *            The heap-object pointer.
	 * @return The field ID in the heap type of the heap-object that the given
	 *         pointer refers to.
	 */
	private Pair<Integer, Integer> getMallocIndex(SymbolicExpression pointer) {
		// ref points to element 0 of an array:
		NTReferenceExpression ref = (NTReferenceExpression) symbolicUtil
				.getSymRef(pointer);
		// objectPointer points to array:
		ArrayElementReference objectPointer = (ArrayElementReference) ref
				.getParent();
		int mallocIndex = ((IntegerNumber) universe.extractNumber(objectPointer
				.getIndex())).intValue();
		// fieldPointer points to the field:
		TupleComponentReference fieldPointer = (TupleComponentReference) objectPointer
				.getParent();
		int mallocId = fieldPointer.getIndex().getInt();

		return new Pair<>(mallocId, mallocIndex);
	}
}
