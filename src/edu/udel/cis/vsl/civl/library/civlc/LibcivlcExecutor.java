package edu.udel.cis.vsl.civl.library.civlc;

import java.util.LinkedList;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.DynamicWriteSet;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Implementation of the execution for system functions declared civlc.h.
 * 
 * @author siegel
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibcivlcExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {
	private Evaluator errSideEffectFreeEvaluator;

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
		this.errSideEffectFreeEvaluator = Semantics
				.newErrorSideEffectFreeEvaluator(modelFactory, stateFactory,
						libEvaluatorLoader, libExecutorLoader, symbolicUtil,
						symbolicAnalyzer, stateFactory.memUnitFactory(),
						errorLogger, civlConfig);
	}

	/*
	 * ******************** Methods from BaseLibraryExecutor *******************
	 */
	@Override
	public Evaluation execute(State state, int pid, CallOrSpawnStatement call,
			String functionName) throws UnsatisfiablePathConditionException {
		Evaluation eval;
		LHSExpression lhs = call.lhs();
		Location target = call.target();
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		String process = state.getProcessState(pid).name();
		Evaluator theEvaluator = evaluator;

		numArgs = call.arguments().size();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		if (functionName.equals("$assume")
				|| functionName.equals("$assume_push")
				|| functionName.equals("$assume_pop")
				|| functionName.equals("$assert"))
			theEvaluator = this.errSideEffectFreeEvaluator;
		for (int i = 0; i < numArgs; i++) {
			arguments[i] = call.arguments().get(i);
			eval = theEvaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		eval = this.executeValue(state, pid, process, call.getSource(),
				functionName, arguments, argumentValues);
		state = eval.state;
		if (lhs != null && eval.value != null)
			state = this.primaryExecutor.assign(state, pid, process, lhs,
					eval.value);
		if (target != null && !state.getProcessState(pid).hasEmptyStack())
			state = this.stateFactory.setLocation(state, pid, target);
		eval.state = state;
		return eval;
	}

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$assert" :
				state = this.executeAssert(state, pid, process, arguments,
						argumentValues, source);
				callEval = new Evaluation(state, null);
				break;
			case "$assume_push" :
				callEval = executeAssumePush(state, pid, arguments,
						argumentValues, source);
				break;
			case "$assume_pop" :
				callEval = executeAssumePop(state, pid, arguments,
						argumentValues, source);
				break;
			case "$assume" :
				callEval = this.executeAssume(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$choose_int_work" :
				callEval = new Evaluation(state, argumentValues[0]);
				break;
			case "$exit" :// return immediately since no transitions needed
							// after an
				// exit, because the process no longer exists.
				callEval = executeExit(state, pid);
				break;
			case "$get_state" :
				callEval = this.executeGetState(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$free" :
				callEval = executeFree(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$havoc" :
				callEval = executeHavoc(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$havoc_mem" :
				callEval = executeHavocMem(state, pid, arguments,
						argumentValues, source);
				break;
			case "$is_concrete_int" :
				callEval = this.executeIsConcreteInt(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$is_derefable" :
				callEval = this.executeIsDerefable(state, pid, process,
						arguments, argumentValues);
				break;
			case "$is_terminated" :
				callEval = this.executeIsTerminated(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$pathCondition" :
				callEval = this.executePathCondition(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$pow" :
			case "$powr" :
				callEval = this.executePow(state, pid, process, arguments,
						argumentValues);
				break;
			case "$proc_defined" :
				callEval = this.executeProcDefined(state, pid, process,
						arguments, argumentValues);
				break;
			case "$scope_defined" :
				callEval = this.executeScopeDefined(state, pid, process,
						arguments, argumentValues);
				break;
			case "$wait" :
				callEval = executeWait(state, pid, arguments, argumentValues,
						source);
				break;
			case "$waitall" :
				callEval = executeWaitAll(state, pid, arguments, argumentValues,
						source);
				break;
			case "$write_set_push" :
				callEval = executeWriteSetPush(state, pid, arguments,
						argumentValues, source);
				break;
			case "$write_set_pop" :
				callEval = executeWriteSetPop(state, pid, arguments,
						argumentValues, source);
				break;
			case "$variable_reference" :
				callEval = executeVariableReference(state, pid, process,
						arguments, argumentValues);
				break;
			case "$next_time_count" :
				callEval = this.executeNextTimeCount(state, pid, process,
						arguments, argumentValues);
				break;
			default :
				throw new CIVLInternalException(
						"Unknown civlc function: " + name, source);
		}
		return callEval;
	}

	/* ************************** Private Methods ************************** */

	private Evaluation executeGetState(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		int stateID = this.stateFactory.saveState(state).left;

		return new Evaluation(state, modelFactory.stateValue(stateID));
	}

	private Evaluation executeIsDerefable(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues) {
		SymbolicExpression result = this.symbolicAnalyzer
				.isDerefablePointer(state, argumentValues[0]).left;

		return new Evaluation(state, result);
	}

	private Evaluation executeIsTerminated(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		SymbolicExpression proc = argumentValues[0];
		int processID = this.modelFactory.getProcessId(proc);
		SymbolicExpression result = this.trueValue;

		if (processID >= 0 && processID < state.numProcs()) {
			if (!state.getProcessState(processID).hasEmptyStack())
				result = this.falseValue;
		}
		return new Evaluation(state, result);
	}

	private Evaluation executeHavoc(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0];
		Pair<BooleanExpression, ResultType> checkPointer = symbolicAnalyzer
				.isDerefablePointer(state, pointer);

		if (checkPointer.right != ResultType.YES)
			state = this.errorLogger.logError(source, state, pid,
					this.symbolicAnalyzer.stateInformation(state),
					checkPointer.left, checkPointer.right,
					ErrorKind.MEMORY_MANAGE,
					"can't apply $havoc to a pointer that can't be dereferenced.\npointer: "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, pointer));

		Evaluation havocEval;
		CIVLType objType = symbolicAnalyzer.civlTypeOfObjByPointer(source,
				state, pointer);
		TypeEvaluation teval = evaluator.getDynamicType(state, pid, objType,
				source, false);

		havocEval = this.evaluator.havoc(teval.state, teval.type);
		state = this.primaryExecutor.assign(source, havocEval.state, pid,
				pointer, havocEval.value);
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$havoc_mem($mem m)</code>. <br>
	 * <br>
	 * Semantics: The function assigns a fresh new symbolic constant to every
	 * memory location in the memory location set represented by m. <br>
	 * 
	 * Notice that currently we do an <strong>compromise</strong> for refreshing
	 * array elements in m: For an array element e in array a in m, we do NOT
	 * assign e a fresh new constant but instead assign the array a a fresh new
	 * constant. The reason is: A non-concrete array write will prevent states
	 * from being canonicalized into a seen state. For example:
	 * 
	 * <code>
	 * $input int N, X;
	 * $assume(N > 0 && X > 0 && N > X);
	 * int a[N];
	 * 
	 * LOOP_0: while (true) {
	 *   a[X] = 0;
	 *   $havoc(&a[X]);
	 * }
	 * 
	 * LOOP_1: while (true) {
	 *   a[X] = 0;
	 *   $havoc(&a);
	 * }
	 * </code> Loop 1 will never converge but the value of a keeps growing. Loop
	 * 2 will converge.
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeHavocMem(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression memObj = argumentValues[0];
		NumericExpression memSize;
		SymbolicExpression pointerArray;
		Number memSizeConcrete;
		Evaluation eval = null;

		// mem obj structure:
		// struct _mem {
		// int size;
		// void * ptrArray[];
		// }
		memSize = (NumericExpression) universe.tupleRead(memObj, zeroObject);
		pointerArray = universe.tupleRead(memObj, oneObject);
		memSizeConcrete = universe.extractNumber(memSize);
		assert memSizeConcrete != null : "The size of $mem obj shall never be non-concrete";

		int memSizeInt = ((IntegerNumber) memSizeConcrete).intValue();
		Expression memObjExpr = arguments[0];

		for (int i = 0; i < memSizeInt; i++) {
			SymbolicExpression pointer = universe.arrayRead(pointerArray,
					universe.integer(i));
			SymbolicType pointedType;
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);

			// compromise: if the given pointer points to an array element,
			// havoc the whole array:
			if (symRef.isArrayElementReference()
					&& !symbolicUtil.isPointer2MemoryBlock(pointer))
				pointer = symbolicUtil.parentPointer(pointer);
			// some dyscopes referred by the pointer may gone already:
			if (stateFactory
					.getDyscopeId(symbolicUtil.getScopeValue(pointer)) >= 0) {
				pointedType = symbolicAnalyzer.dynamicTypeOfObjByPointer(
						memObjExpr.getSource(), state, pointer);
				eval = evaluator.havoc(state, pointedType);
				state = primaryExecutor.assign(source, eval.state, pid, pointer,
						eval.value);
			}
		}
		if (eval != null) {
			eval.value = null;
			eval.state = state;
		}
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
		BooleanExpression result = value.operator() == SymbolicOperator.CONCRETE
				? this.trueValue
				: this.falseValue;
		if (result.isTrue()) {
			Reasoner reasoner = universe
					.reasoner(state.getPathCondition(universe));

			result = reasoner.extractNumber((NumericExpression) value) != null
					? trueValue
					: falseValue;
		}
		return new Evaluation(state, result);
	}

	private Evaluation executePathCondition(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		if (this.civlConfig.enablePrintf())
			this.civlConfig.out()
					.println("path condition: " + this.symbolicAnalyzer
							.symbolicExpressionToString(source, state, null,
									state.getPathCondition(universe)));
		return new Evaluation(state, null);
	}

	private Evaluation executeAssume(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		BooleanExpression assumeValue = (BooleanExpression) argumentValues[0];

		state = stateFactory.addToPathcondition(state, pid, assumeValue);
		return new Evaluation(state, null);
	}

	private Evaluation executeNextTimeCount(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Variable timeCountVar = this.modelFactory.timeCountVariable();
		NumericExpression timeCountValue = (NumericExpression) state
				.valueOf(pid, timeCountVar);

		state = stateFactory.setVariable(state, timeCountVar, pid,
				universe.add(timeCountValue, one));
		return new Evaluation(state, timeCountValue);
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
		int procValue = modelFactory.getProcessId(argumentValues[0]);
		SymbolicExpression result = modelFactory.isPocessIdDefined(procValue)
				? trueValue
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
	private Evaluation executeScopeDefined(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		int scopeValue = stateFactory.getDyscopeId(argumentValues[0]);
		SymbolicExpression result = stateFactory.isScopeIdDefined(scopeValue)
				? trueValue
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
	private Evaluation executeWait(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source) {
		SymbolicExpression procVal = argumentValues[0];
		int joinedPid = modelFactory.getProcessId(procVal);

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
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
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
			CIVLSource procsSource = arguments[0].getSource();
			Evaluation eval;

			for (int i = 0; i < numOfProcs_int; i++) {
				NumericExpression offSetV = universe.integer(i);
				SymbolicExpression procPointer, proc;
				int pidValue;

				eval = evaluator.arrayElementReferenceAdd(state, pid,
						procsPointer, offSetV, procsSource).left;
				procPointer = eval.value;
				state = eval.state;
				eval = evaluator.dereference(procsSource, state, process,
						typeFactory.processType(), procPointer, false, true);
				proc = eval.value;
				state = eval.state;
				pidValue = modelFactory.getProcessId(proc);
				if (!modelFactory.isProcessIdNull(pidValue)
						&& modelFactory.isPocessIdDefined(pidValue))
					state = stateFactory.removeProcess(state, pidValue);
			}
		}
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$assume_push()</code>. <br>
	 * <br>
	 * 
	 * Push a boolean expression as a partial path condition onto the partial
	 * path condition stack associated with the calling process.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeAssumePush(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		BooleanExpression assumeValue = (BooleanExpression) argumentValues[0];

		state = stateFactory.pushAssumption(state, pid, assumeValue);
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$assume_pop()</code>. <br>
	 * <br>
	 * 
	 * Pop a partial path condition out of the partial path condition stack
	 * associated with the calling process.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeAssumePop(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		state = stateFactory.popAssumption(state, pid);
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$write_set_push()</code>. <br>
	 * <br>
	 * 
	 * Push an empty write set onto write set stack associated with the calling
	 * process.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeWriteSetPush(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		state = stateFactory.pushEmptyWrite(state, pid);
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$write_set_pop($mem * m)</code>. <br>
	 * <br>
	 * 
	 * Pop a write set w out of the write set stack associated with the calling
	 * process. Assign write set w' to the object refered by the given reference
	 * m, where w' is a subset of w. <code>w - w'</code> is a set of unreachable
	 * memory locaiton references.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeWriteSetPop(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression memPointer = argumentValues[0];
		String process = state.getProcessState(pid).name();
		CIVLType memType = typeFactory.systemType(ModelConfiguration.MEM_TYPE);
		Evaluation eval = evaluator.dereference(source, state, process, memType,
				memPointer, false, true);

		state = eval.state;

		SymbolicExpression memValue = eval.value;
		SymbolicExpression pointerArray;
		SymbolicTupleType memValueType;
		LinkedList<SymbolicExpression> memValueComponents = new LinkedList<>();
		DynamicWriteSet writeSet = stateFactory.peekWriteSet(state, pid);
		int size = 0;

		state = stateFactory.popWriteSet(state, pid);
		memValueType = (SymbolicTupleType) memType.getDynamicType(universe);
		for (SymbolicExpression pointer : writeSet) {
			SymbolicExpression referredScopeValue = symbolicUtil
					.getScopeValue(pointer);
			int referredDyscope = stateFactory.getDyscopeId(referredScopeValue);

			if (referredDyscope < 0)
				continue;
			memValueComponents.add(pointer);
			size++;
		}
		pointerArray = universe.array(typeFactory.pointerSymbolicType(),
				memValueComponents);
		memValueComponents.clear();
		memValueComponents.add(universe.integer(size));
		memValueComponents.add(pointerArray);
		memValue = universe.tuple(memValueType, memValueComponents);
		state = primaryExecutor.assign(source, state, pid, memPointer,
				memValue);
		eval.state = state;
		eval.value = null;
		return eval;
	}

	private State executeAssert(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		BooleanExpression assertValue = (BooleanExpression) argumentValues[0];
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		reasoner = universe.reasoner(state.getPathCondition(universe));
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();

		if (resultType != ResultType.YES
				|| !modelFactory.getAllACSLPredicates().isEmpty()) {
			assertValue.setValidity(null);

			Reasoner why3Reasoner = universe.why3Reasoner(
					state.getPathCondition(universe),
					ACSLPredicateEvaluator.evaluateACSLPredicate(
							modelFactory.getAllACSLPredicates(), state, pid,
							errSideEffectFreeEvaluator));

			if (why3Reasoner != reasoner)
				resultType = why3Reasoner.valid(assertValue).getResultType();
			// resultType = HeuristicProveHelper.heuristicsValid(reasoner,
			// universe, assertValue);
		}
		if (resultType != ResultType.YES) {
			// uncomment the following for debugging:
			// Why3Translator translator = new Why3Translator(
			// (PreUniverse) universe, state.getPathCondition(universe),
			// new ProverPredicate[0]);
			// String goal = translator.translateGoal(assertValue);
			//
			// System.out.println(translator.getExecutableOutput(
			// universe.numProverValidCalls() - 1, goal));
			StringBuilder message = new StringBuilder();
			Pair<State, String> messageResult = this.symbolicAnalyzer
					.expressionEvaluation(state, pid, arguments[0], false);
			String firstEvaluation, secondEvaluation, result;

			state = messageResult.left;
			message.append("Assertion: ");
			message.append(arguments[0]);
			message.append("\n        -> ");
			message.append(messageResult.right);
			firstEvaluation = messageResult.right;
			messageResult = this.symbolicAnalyzer.expressionEvaluation(state,
					pid, arguments[0], true);
			state = messageResult.left;
			secondEvaluation = messageResult.right;
			if (!firstEvaluation.equals(secondEvaluation)) {
				message.append("\n        -> ");
				message.append(secondEvaluation);
			}
			result = this.symbolicAnalyzer
					.symbolicExpressionToString(arguments[0].getSource(), state,
							null, assertValue)
					.toString();
			if (!secondEvaluation.equals(result)) {
				message.append("\n        -> ");
				message.append(result);
			}
			state = this.reportAssertionFailure(state, pid, process, resultType,
					message.toString(), arguments, argumentValues, source,
					assertValue, 1);
			state = stateFactory.addToPathcondition(state, pid,
					(BooleanExpression) argumentValues[0]);
		}
		return state;
	}
}
