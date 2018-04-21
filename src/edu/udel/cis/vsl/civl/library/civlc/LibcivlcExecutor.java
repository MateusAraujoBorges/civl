package edu.udel.cis.vsl.civl.library.civlc;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.civlc.Heuristics.Query;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
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
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
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
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.prove.IF.ProverPredicate;

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
			case "$heap_size" :
				callEval = executeGetHeapSize(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$exit" :// return immediately since no transitions needed
							// after an
				// exit, because the process no longer exists.
				callEval = executeExit(state, pid);
				break;
			case "$get_state" :
				callEval = executeGetState(state, pid, process, arguments,
						argumentValues, false, source);
				break;
			case "$get_full_state" :
				callEval = executeGetState(state, pid, process, arguments,
						argumentValues, true, source);
				break;
			case "$free" :
				callEval = executeFree(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$havoc" :
				callEval = executeHavoc(state, pid, process, arguments,
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
						"Unknown civlc function: " + functionName, source);
		}
		return callEval;
	}

	/* ************************** Private Methods ************************** */
	/**
	 * <p>
	 * The <code>$heap_size($scope s)</code> system function returns the size of
	 * the heap of the given scope.
	 * </p>
	 * <p>
	 * The heap value is a tuple of 2d-arrays. Each tuple field is associated to
	 * a unique lexical "malloc". The heap size is computed with the following
	 * algorithm:<code>
	 *   for each tule-field t:
	 *     for each 2d-array element e: 
	 *       result += sizeof(e);
	 * </code> Note that the extent of the 2d array must concrete since it is
	 * the number times a same lexical malloc gets called.
	 * </p>
	 * 
	 * @return the evaluation of this function call.
	 */
	private Evaluation executeGetHeapSize(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		int dyscopeId = stateFactory.getDyscopeId(argumentValues[0]);
		DynamicScope dyscope = state.getDyscope(dyscopeId);
		SymbolicExpression heap = dyscope.getValue(0);

		// computing heap size:
		SymbolicTupleType heapTupleType = (SymbolicTupleType) heap.type();
		SymbolicTypeSequence typesInHeap = heapTupleType.sequence();
		int numTypes = typesInHeap.numTypes();
		NumericExpression result = universe.zeroInt();

		for (int i = 0; i < numTypes; i++) {
			SymbolicExpression array2d, array1d;
			SymbolicType elementType;
			int array2dExtent; // must be concrete

			array2d = universe.tupleRead(heap, universe.intObject(i));
			elementType = ((SymbolicArrayType) ((SymbolicArrayType) array2d
					.type()).elementType()).elementType();
			array2dExtent = ((IntegerNumber) universe
					.extractNumber(universe.length(array2d))).intValue();
			for (int j = 0; j < array2dExtent; j++) {
				array1d = universe.arrayRead(array2d, universe.integer(j));
				if (array1d == symbolicUtil.invalidHeapObject(array1d.type()))
					continue;
				result = universe.add(result, universe.multiply(
						universe.length(array1d),
						symbolicUtil.sizeof(source, null, elementType)));
			}
		}
		return new Evaluation(state, result);
	}

	private Evaluation executeGetState(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			boolean isFull, CIVLSource source) {
		int topDyscope = state.getProcessState(pid).peekStack().scope();
		State snapshot = isFull
				? state
				: stateFactory.getStateSnapshot(state, pid, topDyscope);
		int snapshotStateID = stateFactory.saveState(snapshot).left;

		return new Evaluation(state, modelFactory.stateValue(snapshotStateID));
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
						procPointer, false, true);
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

	private State executeAssert(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		BooleanExpression assertValue = (BooleanExpression) argumentValues[0];
		BooleanExpression context = state.getPathCondition(universe);
		ResultType resultType = ResultType.MAYBE;
		ProverPredicate[] acslPredicates2why3 = ACSLPredicateEvaluator
				.evaluateACSLPredicate(modelFactory.getAllACSLPredicates(),
						state, pid, errSideEffectFreeEvaluator);

		if (!civlConfig.prob()) {
			Query query = (new Heuristics(universe))
					.applyHeuristicSimplifications(context, assertValue);

			if (acslPredicates2why3.length == 0)
				resultType = universe.reasoner(query.context).valid(query.query)
						.getResultType();
			if (resultType == ResultType.MAYBE)
				resultType = universe
						.why3Reasoner(query.context, acslPredicates2why3)
						.valid(query.query).getResultType();
			if (resultType == ResultType.MAYBE) {
				UniversalNormalization uniNorm = new UniversalNormalization(
						universe);

				context = (BooleanExpression) uniNorm.apply(query.context);
				assertValue = (BooleanExpression) uniNorm.apply(query.query);
				resultType = universe.why3Reasoner(context, acslPredicates2why3)
						.valid(assertValue).getResultType();
			}
		} else
			resultType = universe.reasoner(context).valid(assertValue)
					.getResultType();
		if (resultType != ResultType.YES) {
			// uncomment the following when debug:
			// PreUniverse preU = (PreUniverse) universe;
			// Why3Translator trans = new Why3Translator(preU,
			// preU.cleanBoundVariables(context), acslPredicates2why3);
			// String goals[];
			//
			// assertValue = (BooleanExpression) preU
			// .cleanBoundVariables(assertValue);
			// if (assertValue.operator() == SymbolicOperator.AND) {
			// goals = new String[assertValue.numArguments()];
			// for (int i = 0; i < goals.length; i++)
			// goals[i] = trans.translateGoal(
			// (SymbolicExpression) assertValue.argument(i));
			// } else {
			// goals = new String[1];
			// goals[0] = trans.translateGoal(assertValue);
			// }
			// System.out.println(trans.getExecutableOutput(
			// universe.numProverValidCalls(), goals));

			StringBuilder message = new StringBuilder();
			Pair<State, String> messageResult = this.symbolicAnalyzer
					.expressionEvaluation(state, pid, arguments[0], false);
			String firstEvaluation, secondEvaluation, result;

			state = messageResult.left;
			message.append("Assertion: ");
			message.append(arguments[0]);
			message.append("\n -> ");
			message.append(messageResult.right);
			firstEvaluation = messageResult.right;
			messageResult = this.symbolicAnalyzer.expressionEvaluation(state,
					pid, arguments[0], true);
			state = messageResult.left;
			secondEvaluation = messageResult.right;
			if (!firstEvaluation.equals(secondEvaluation)) {
				message.append("\n -> ");
				message.append(secondEvaluation);
			}
			result = this.symbolicAnalyzer
					.symbolicExpressionToString(arguments[0].getSource(), state,
							null, assertValue)
					.toString();
			if (!secondEvaluation.equals(result)) {
				message.append("\n -> ");
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
