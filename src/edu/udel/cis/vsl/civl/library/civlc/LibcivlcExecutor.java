package edu.udel.cis.vsl.civl.library.civlc;

import java.math.BigInteger;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

/**
 * Implementation of the execution for system functions declared civlc.h.
 * 
 * @author siegel
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library executor for civlc.h.
	 * 
	 * @param name
	 *            The name of the library, which is concurrency.
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param civlConfig
	 *            The CIVL configuration configured by the user.
	 */
	public LibcivlcExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	/* ******************** Methods from BaseLibraryExecutor ******************* */

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
		case "$assert":
			state = this.executeAssert(state, pid, process, arguments,
					argumentValues, source);
			callEval = new Evaluation(state, null);
			break;
		case "$assume":
			callEval = this.executeAssume(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$choose_int_work":
			callEval = new Evaluation(state, argumentValues[0]);
			break;
		case "$defined":
			callEval = executeDefined(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$exit":// return immediately since no transitions needed after an
			// exit, because the process no longer exists.
			callEval = executeExit(state, pid);
			break;
		case "$free":
		case "$int_iter_destroy":
			callEval = executeFree(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$havoc":
			callEval = executeHavoc(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$int_iter_create":
			callEval = this.executeIntIterCreate(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$int_iter_hasNext":
			callEval = this.executeIntIterHasNext(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$int_iter_next":
			callEval = this.executeIntIterNext(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$is_concrete_int":
			callEval = this.executeIsConcreteInt(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$pathCondition":
			callEval = this.executePathCondition(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$pow":
		case "$powr":
			callEval = this.executePow(state, pid, process, arguments,
					argumentValues);
			break;
		case "$proc_defined":
			callEval = this.executeProcDefined(state, pid, process, arguments,
					argumentValues);
			break;
		case "$scope_defined":
			callEval = this.executeScopeDefined(state, pid, process, arguments,
					argumentValues);
			break;
		case "$wait":
			callEval = executeWait(state, pid, arguments, argumentValues,
					source);
			break;
		case "$waitall":
			callEval = executeWaitAll(state, pid, arguments, argumentValues,
					source);
			break;
		case "$variable_reference":
			callEval = executeVariableReference(state, pid, process, arguments,
					argumentValues);
			break;
		case "$next_time_count":
			callEval = this.executeNextTimeCount(state, pid, process,
					arguments, argumentValues);
			break;
		default:
			throw new CIVLInternalException("Unknown civlc function: " + name,
					source);
		}
		return callEval;
	}

	/* ************************** Private Methods ************************** */

	private Evaluation executeHavoc(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0];
		CIVLType type;
		Pair<BooleanExpression, ResultType> checkPointer = symbolicAnalyzer
				.isDerefablePointer(state, pointer);

		if (checkPointer.right != ResultType.YES)
			state = this.errorLogger.logError(
					source,
					state,
					process,
					this.symbolicAnalyzer.stateInformation(state),
					checkPointer.left,
					checkPointer.right,
					ErrorKind.MEMORY_MANAGE,
					"can't apply $havoc to a pointer that can't be dereferenced.\npointer: "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, pointer));

		Evaluation havocEval;

		type = this.symbolicAnalyzer.typeOfObjByPointer(source, state, pointer);
		havocEval = this.evaluator.havoc(state, type.getDynamicType(universe));
		state = this.primaryExecutor.assign(source, havocEval.state, process,
				pointer, havocEval.value);
		return new Evaluation(state, null);
	}

	private Evaluation executePow(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result = this.universe.power(
				(NumericExpression) argumentValues[0],
				(NumericExpression) argumentValues[1]);

		return new Evaluation(state, result);
	}

	private Evaluation executeVariableReference(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues) {
		// TODO Auto-generated method stub
		// dd
		return null;
	}

	private Evaluation executeIsConcreteInt(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression value = argumentValues[0];
		BooleanExpression result = value.operator() == SymbolicOperator.CONCRETE ? this.trueValue
				: this.falseValue;

		return new Evaluation(state, result);
	}

	private Evaluation executePathCondition(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (this.civlConfig.enablePrintf())
			this.civlConfig.out().println(
					"path condition: "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null,
									state.getPathCondition()));
		return new Evaluation(state, null);
	}

	private Evaluation executeDefined(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0], result = trueValue;
		Evaluation eval = this.evaluator.dereference(arguments[0].getSource(),
				state, process, arguments[0], pointer, false);

		state = eval.state;
		if (eval.value.isNull()) {
			result = falseValue;
		}
		return new Evaluation(state, result);
	}

	private Evaluation executeAssume(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		BooleanExpression assumeValue = (BooleanExpression) argumentValues[0];
		BooleanExpression oldPathCondition, newPathCondition;

		oldPathCondition = state.getPathCondition();
		newPathCondition = (BooleanExpression) universe.canonic(universe.and(
				oldPathCondition, assumeValue));
		state = state.setPathCondition(newPathCondition);
		return new Evaluation(state, null);
	}

	private Evaluation executeNextTimeCount(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Variable timeCountVar = this.modelFactory.timeCountVariable();
		NumericExpression timeCountValue = (NumericExpression) state.valueOf(
				pid, timeCountVar);

		state = stateFactory.setVariable(state, timeCountVar, pid,
				universe.add(timeCountValue, one));
		return new Evaluation(state, timeCountValue);
	}

	/**
	 * Creates a new iterator for an array of integers, and returns the handle
	 * of the iterator. The new object will be allocated in the given scope.<br>
	 * <code>$int_iter $int_iter_create($scope scope, int *array, int
	 * size);</code>
	 * 
	 * <code>
	 * typedef struct __int_iter__ {<br>
	 * &nbsp;&nbsp;int size;<br>
	 * &nbsp;&nbsp;int content[];<br>
	 * &nbsp;&nbsp;int index; //initialized as 0<br>
	 * } $int_iter;
	 * </code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private Evaluation executeIntIterCreate(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression intIterObj;
		SymbolicExpression size = argumentValues[2];
		SymbolicExpression currentIndex = universe.integer(0);
		SymbolicExpression scope = argumentValues[0];
		Expression scopeExpression = arguments[0];
		SymbolicExpression arrayPointer = argumentValues[1];
		Expression arrayPointerExpression = arguments[1];
		SymbolicExpression intArray;
		LinkedList<SymbolicExpression> intArrayComponents = new LinkedList<>();
		List<SymbolicExpression> intIterComponents = new LinkedList<>();
		int int_size;
		CIVLType intIterType = typeFactory
				.systemType(ModelConfiguration.INT_ITER_TYPE);
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_size = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) size);
		Evaluation eval = evaluator.dereference(source, state, process,
				arguments[1], arrayPointer, false);
		CIVLSource arrayPointerSource = arrayPointerExpression.getSource();

		state = eval.state;
		if (number_size != null)
			int_size = number_size.intValue();
		else
			throw new CIVLInternalException(
					"Cannot extract concrete int value for gbarrier size",
					arguments[1]);
		for (int i = 0; i < int_size; i++) {
			BinaryExpression pointerAdditionExpression = modelFactory
					.binaryExpression(arrayPointerExpression.getSource(),
							BINARY_OPERATOR.POINTER_ADD,
							arrayPointerExpression, modelFactory
									.integerLiteralExpression(
											arrayPointerExpression.getSource(),
											BigInteger.valueOf(i)));
			SymbolicExpression arrayElePointer;

			eval = evaluator.pointerAdd(state, pid, process,
					pointerAdditionExpression, arrayPointer,
					universe.integer(i));
			state = eval.state;
			arrayElePointer = eval.value;
			eval = evaluator.dereference(arrayPointerSource, state, process,
					pointerAdditionExpression, arrayElePointer, false);
			state = eval.state;
			intArrayComponents.add(eval.value);
		}
		intArray = universe.array(
				typeFactory.integerType().getDynamicType(universe),
				intArrayComponents);
		intIterComponents.add(size);
		intIterComponents.add(intArray);
		intIterComponents.add(currentIndex);
		intIterObj = universe.tuple(
				(SymbolicTupleType) intIterType.getDynamicType(universe),
				intIterComponents);
		return primaryExecutor.malloc(source, state, pid, process,
				scopeExpression, scope, intIterType, intIterObj);
	}

	/**
	 * Tells whether the integer iterator has any more elements.
	 * <code>_Bool $int_iter_hasNext($int_iter iter);</code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private Evaluation executeIntIterHasNext(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression iterHandle = argumentValues[0];
		SymbolicExpression iterObj;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;
		NumericExpression size, index;
		SymbolicExpression hasNext;

		eval = evaluator.dereference(civlsource, state, process, arguments[0],
				iterHandle, false);
		state = eval.state;
		iterObj = eval.value;
		size = (NumericExpression) universe.tupleRead(iterObj, zeroObject);
		index = (NumericExpression) universe.tupleRead(iterObj, twoObject);
		hasNext = universe.lessThan(index, size);
		return new Evaluation(state, hasNext);
	}

	/**
	 * Returns the next element in the iterator (and updates the iterator).
	 * <code>int $int_iter_next($int_iter iter);</code>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
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
	private Evaluation executeIntIterNext(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression iterHandle = argumentValues[0];
		SymbolicExpression array;
		SymbolicExpression iterObj;
		CIVLSource civlsource = arguments[0].getSource();
		Evaluation eval;
		NumericExpression index;
		SymbolicExpression nextInt;

		eval = evaluator.dereference(civlsource, state, process, arguments[0],
				iterHandle, false);
		state = eval.state;
		iterObj = eval.value;
		array = universe.tupleRead(iterObj, oneObject);
		index = (NumericExpression) universe.tupleRead(iterObj, twoObject);
		nextInt = universe.arrayRead(array, index);
		// updates iterator object
		index = universe.add(index, one);
		iterObj = universe.tupleWrite(iterObj, twoObject, index);
		state = primaryExecutor.assign(source, state, process, iterHandle,
				iterObj);
		return new Evaluation(state, nextInt);
	}

	/**
	 * Checks if a process reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeProcDefined(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		int procValue = modelFactory.getProcessId(arguments[0].getSource(),
				argumentValues[0]);
		SymbolicExpression result = modelFactory.isPocessIdDefined(procValue) ? trueValue
				: falseValue;

		return new Evaluation(state, result);
	}

	/**
	 * Checks if a scope reference is defined, i.e., its id is non-negative.
	 * 
	 * @param state
	 *            The state where the checking happens.
	 * @param pid
	 *            The ID of the process that this computation belongs to.
	 * @param lhs
	 *            The left hand side expression of this function call.
	 * @param arguments
	 *            The static arguments of the function call.
	 * @param argumentValues
	 *            The symbolic values of the arguments of the function call
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeScopeDefined(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		int scopeValue = modelFactory.getScopeId(arguments[0].getSource(),
				argumentValues[0]);
		SymbolicExpression result = modelFactory.isScopeIdDefined(scopeValue) ? trueValue
				: falseValue;

		return new Evaluation(state, result);
	}

	/**
	 * Executes the $wait system function call. Only enabled when the waited
	 * process has terminated.
	 * 
	 * * @param state The current state.
	 * 
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
	 * @param target
	 *            The target location of the wait function call.
	 * @return The new state after executing the function call.
	 * @return
	 */
	private Evaluation executeWait(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		SymbolicExpression procVal = argumentValues[0];
		int joinedPid = modelFactory.getProcessId(arguments[0].getSource(),
				procVal);

		// state = stateFactory.setLocation(state, pid, target);
		if (modelFactory.isPocessIdDefined(joinedPid)
				&& !modelFactory.isProcessIdNull(joinedPid))
			state = stateFactory.removeProcess(state, joinedPid);
		return new Evaluation(state, null);
	}

	private Evaluation executeWaitAll(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression procsPointer = argumentValues[0];
		SymbolicExpression numOfProcs = argumentValues[1];
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		IntegerNumber number_nprocs = (IntegerNumber) reasoner
				.extractNumber((NumericExpression) numOfProcs);
		String process = state.getProcessState(pid).name() + "(id=" + pid + ")";

		if (number_nprocs == null) {
			this.errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"the number of processes for $waitall "
							+ "shoud be a concrete value");
			throw new UnsatisfiablePathConditionException();
		} else {
			int numOfProcs_int = number_nprocs.intValue();
			BinaryExpression pointerAdd;
			CIVLSource procsSource = arguments[0].getSource();
			Evaluation eval;

			for (int i = 0; i < numOfProcs_int; i++) {
				Expression offSet = modelFactory.integerLiteralExpression(
						procsSource, BigInteger.valueOf(i));
				NumericExpression offSetV = universe.integer(i);
				SymbolicExpression procPointer, proc;
				int pidValue;

				pointerAdd = modelFactory.binaryExpression(procsSource,
						BINARY_OPERATOR.POINTER_ADD, arguments[0], offSet);
				eval = evaluator.pointerAdd(state, pid, process, pointerAdd,
						procsPointer, offSetV);
				procPointer = eval.value;
				state = eval.state;
				eval = evaluator.dereference(procsSource, state, process,
						pointerAdd, procPointer, false);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(procsSource, proc);
				if (!modelFactory.isProcessIdNull(pidValue)
						&& modelFactory.isPocessIdDefined(pidValue))
					state = stateFactory.removeProcess(state, pidValue);
			}
		}
		return new Evaluation(state, null);
	}

}
