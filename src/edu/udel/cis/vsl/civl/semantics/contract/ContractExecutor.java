package edu.udel.cis.vsl.civl.semantics.contract;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractedFunctionCallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractedFunctionCallStatement.CONTRACTED_FUNCTION_CALL_KIND;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.common.CommonExecutor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * <p>
 * <b> Contracts system execution semantics:</b> A contracts system verifies
 * functions independently. The verification of a function f relies on the
 * function body of f , the function contracts of f and the function contracts
 * of all other functions that called inside the body of f. To verify f, all
 * requirements specified in the function contracts of f are assumed to true,
 * all ensurances specified in function contracts of f will be checked
 * immediately before the control returns from f. Once a function call on a
 * function f' is encountered, the function contracts of f' is used.
 * Requirements specified in function contracts of f' are checked immediately
 * after the call stack pushed; ensurances specified in function contracts of f'
 * are assumed to true immediately before the call stack popped. Once a function
 * call on a function f'' is encountered and f'' has no function contracts,
 * symbolic execution on the body of f'' will be applied.
 * 
 * The execution semantics are different from regular CIVL-C language semantics,
 * thus this class extends and overrides some methods of the
 * {@link CommonExecutor}.
 * 
 * Methods for executing contracts system semantics are organized as follows:
 * <ul>
 * <b>Top layer: Methods that are fit in CIVL's design, will be used by CIVL
 * executor directly.</b>
 * <li>{@link #executeReturn(State, int, String, ReturnStatement)}</li>
 * <li>
 * {@link #executeContractedFunctionCallEnter(State, int, String, ContractedFunctionCallStatement)}
 * </li>
 * <li>
 * {@link #executeContractedFunctionCallExit(State, int, String, ContractedFunctionCallStatement)}
 * </li>
 * <li>
 * {@link #executeContractVerifyCall(State, int, String, ContractVerifyStatement)}
 * </li>
 * </ul>
 * <ul>
 * <b>Middle layer: Methods that are used by top layer. Middle layer methods
 * deal with checking and assuming contract clauses.</b>
 * <li>{@link #inferByContracts(State, int, String, String, FunctionContract)}</li>
 * <li>
 * {@link #generateConditionsForContracts(State, int, String, CIVLFunction, FunctionContract)}
 * </li>
 * <li>{@link #conditionGenerationWorker(State, int, String, Iterable)}</li>
 * <li>{@link #verifyLocalContractClauses(State, int, String, String, Iterable)}
 * </li>
 * <li>{@link #assumeLocalContractClauses(State, int, String, String, Iterable)}
 * </li>
 * <li>
 * {@link #assumeWithPartialCollectiveEvaluation(State, int, String, String, Iterable, Expression)}
 * </li>
 * <li>
 * {@link #verifyContractsAtReturn(State, int, String, CIVLFunction, FunctionContract)}
 * </li>
 * </ul>
 * <ul>
 * <b>Low layer: Generic methods for executing (partial) collective evaluation
 * algorithms.</b>
 * <li>
 * {@link #executeCollectiveContract(State, int, String, Iterable, ContractKind, MPICollectiveBehavior, CIVLSource)}
 * </li>
 * <li>
 * {@link #executePartialCollectiveContract(State, int, String, Iterable, Expression, ContractKind, CIVLSource)}
 * </li>
 * </ul>
 * </p>
 * 
 * @author ziqing
 *
 */
public class ContractExecutor extends CommonExecutor implements Executor {
	/**
	 * A reference to a contract evaluator:
	 */
	private ContractEvaluator evaluator;

	/**
	 * A reference to a StateFactory:
	 */
	private StateFactory stateFactory;

	/**
	 * A reference to a symbolic universe:
	 */
	private SymbolicUniverse universe;

	/**
	 * A reference to a symbolic analyzer:
	 */
	private SymbolicAnalyzer symbolicAnalyzer;

	/**
	 * A reference to a symbolic utility:
	 */
	private SymbolicUtility symbolicUtil;

	/**
	 * A reference to an Error logger:
	 */
	private CIVLErrorLogger errorLogger;

	/**
	 * A reference to a CIVL configuration file:
	 */
	private CIVLConfiguration civlConfig;

	/**
	 * A reference to a model factory:
	 */
	private ModelFactory modelFactory;

	/**
	 * A reference to a library executor loader:
	 */
	private LibraryExecutorLoader loader;

	/**
	 * A reference to a {@link ContractContionGenerator}
	 */
	private ContractConditionGenerator conditionGenerator;

	public ContractExecutor(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryExecutorLoader loader,
			ContractEvaluator evaluator, SymbolicAnalyzer symbolicAnalyzer,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig,
			ContractConditionGenerator conditionGenerator) {
		super(modelFactory, stateFactory, loader, evaluator, symbolicAnalyzer,
				errorLogger, civlConfig);
		this.evaluator = evaluator;
		this.stateFactory = stateFactory;
		this.universe = modelFactory.universe();
		this.errorLogger = errorLogger;
		this.civlConfig = civlConfig;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.symbolicUtil = evaluator.symbolicUtility();
		this.modelFactory = modelFactory;
		this.loader = loader;
		this.conditionGenerator = conditionGenerator;
	}

	/**
	 * <p>
	 * <b>Override:</b>
	 * <ul>
	 * <li>Execution of $contractVerify statements.</li>
	 * <li>Execution of contracted function call statements.</li>
	 * </ul>
	 * </p>
	 */
	@Override
	protected State executeStatement(State state, int pid, Statement statement)
			throws UnsatisfiablePathConditionException {
		String process = "p" + pid;

		numSteps++;
		switch (statement.statementKind()) {
		case RETURN:
			return executeReturn(state, pid, process,
					(ReturnStatement) statement);
		case CONTRACT_VERIFY:
			// $contractVerify will be elaborated for bounded symbolic values by
			// the enabler. The elaborated statement is $contractVerify_worker:
			assert ((ContractVerifyStatement) statement).isWorker();
			return executeContractVerifyCall(state, pid, process,
					(ContractVerifyStatement) statement);
		case CONTRACTED_CALL:
			ContractedFunctionCallStatement contractedCall = (ContractedFunctionCallStatement) statement;

			if (contractedCall.getContractedFunctionCallKind().equals(
					CONTRACTED_FUNCTION_CALL_KIND.ENTER))
				return executeContractedFunctionCallEnter(state, pid, process,
						contractedCall);
			else
				return executeContractedFunctionCallExit(state, pid, process,
						contractedCall);
		default:
			return super.executeStatement(state, pid, statement);
		}
	}

	/**
	 * <p>
	 * <b>Override:</b> In contracts system, pointers that not are required as
	 * valid pointers will have the symbolic values in LAMBDA form, thus this
	 * method is override to detect that if the assigned pointer is undefined or
	 * cannot be proved as valid.
	 * </p>
	 */
	@Override
	protected State assign(CIVLSource source, State state, String process,
			SymbolicExpression pointer, SymbolicExpression value,
			boolean isInitialization, boolean toCheckPointer)
			throws UnsatisfiablePathConditionException {
		if (pointer.operator().equals(SymbolicOperator.TUPLE))
			return super.assign(source, state, process, pointer, value,
					isInitialization, toCheckPointer);
		else
			errorLogger.logSimpleError(
					source,
					state,
					process,
					symbolicAnalyzer.stateToString(state),
					ErrorKind.CONTRACT,
					"Attempt to write to a memory location through a pointer "
							+ this.symbolicAnalyzer.symbolicExpressionToString(
									source, state, null, pointer)
							+ "\nwhich can't be proved as a valid pointer.");
		throw new UnsatisfiablePathConditionException();
	}

	/******
	 * Top layer: Execution statements in contracts system execution
	 ******/
	/**
	 * <p>
	 * <b>Summary: </b> Execute a return statement in a contract system.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b> There are two kinds of return statements:
	 * <ul>
	 * <li>A return statement for the function f which is the main verifying
	 * function. Such a return statement is responsible for checking ensurances
	 * in function contracts of f.</li>
	 * <li>A return statement of functions F' which contains all functions f'
	 * that is called during the verification and f' doen't not be specified
	 * function contracts. This should be executed as a regular return
	 * statement.</li>
	 * </ul>
	 * </p>
	 * 
	 * @param state
	 *            The state of the program.
	 * @param pid
	 *            The process id of the currently executing process.
	 * @param statement
	 *            The return statement to be executed.
	 * @return The updated state of the program.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeReturn(State state, int pid, String process,
			ReturnStatement statement)
			throws UnsatisfiablePathConditionException {
		Expression returnedExpr = statement.expression();
		// Symbolic expression for \result expression, if it exists:
		SymbolicExpression returnedValue = null;
		ProcessState processState;
		CIVLFunction function;
		String functionName;

		processState = state.getProcessState(pid);
		function = processState.peekStack().location().function();
		functionName = function.name().name();
		if (function.isAtomicFunction())
			state = stateFactory.leaveAtomic(state, pid);
		if (returnedExpr == null)
			returnedValue = null;
		else {
			Evaluation eval = evaluator.evaluate(state, pid, returnedExpr);

			returnedValue = eval.value;
			state = eval.state;
		}
		// In contracts mode, only function invoked by $contractVerify keyword
		// will reach its' return statement because contracted function call
		// will not be executed in real and non-contracted function call will
		// not get into the following branch:
		if (function.isContracted()) {
			// Assigning \result variable:
			Variable resultVar;

			resultVar = returnedValue != null ? function.outerScope().variable(
					ModelConfiguration.ContractResultName) : null;
			state = resultVar != null ? stateFactory.setVariable(state,
					resultVar, pid, returnedValue) : state;
			// Before pop stack entry frame, verify contracts:
			state = verifyContractsAtReturn(state, pid, process, function,
					function.functionContract());
			// Set MPI status to FINALIZED if it exists:
			state = setMPISysStatusIfExists(state, pid, function.outerScope()
					.parent(), evaluator.FINALIZED);
			// Clean heapObjects allocated for "\valid()":
			state = stateFactory.setVariable(state, function.outerScope()
					.variable(0), pid, universe.nullExpression());
		}
		if (functionName.equals(CIVLConstants.civlSystemFunction)) {
			assert pid == 0;
			if (state.numProcs() > 1) {
				for (ProcessState proc : state.getProcessStates()) {
					if (proc == null)
						continue;
					if (proc.getPid() == pid)
						continue;
					if (!this.civlConfig.svcomp() && !proc.hasEmptyStack()) {
						errorLogger.logSimpleError(statement.getSource(),
								state, process,
								symbolicAnalyzer.stateInformation(state),
								ErrorKind.PROCESS_LEAK,
								"attempt to terminate the main process while "
										+ proc.name() + " is still running");
						throw new UnsatisfiablePathConditionException();
					}
				}
			}
		}
		state = stateFactory.popCallStack(state, pid);
		processState = state.getProcessState(pid);
		if (!processState.hasEmptyStack()) {
			StackEntry returnContext = processState.peekStack();
			Location returnLocation = returnContext.location();
			Statement outgoing = returnLocation.getSoleOutgoing();
			boolean hasLHS;

			// Assigning returned value to LHS:
			if (outgoing.statementKind() == StatementKind.CALL_OR_SPAWN) {
				CallOrSpawnStatement call = (CallOrSpawnStatement) outgoing;

				hasLHS = call.lhs() != null;
				if (hasLHS) {
					if (returnedValue == null) {
						errorLogger
								.logSimpleError(
										call.getSource(),
										state,
										process,
										symbolicAnalyzer
												.stateInformation(state),
										ErrorKind.OTHER,
										"attempt to use the return value of function "
												+ functionName
												+ " when "
												+ functionName
												+ " has returned without a return value.");
						returnedValue = universe.nullExpression();
					}
					state = assign(state, pid, process, call.lhs(),
							returnedValue);
				}
			} else {
				assert outgoing.statementKind() == StatementKind.CONTRACT_VERIFY;
				hasLHS = false;
			}
			state = stateFactory.setLocation(state, pid, outgoing.target(),
					hasLHS);
		}
		return state;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Execute a contracted function call enter statement. This
	 * method pushes a call stack entry into the call stack.
	 * </p>
	 * <p>
	 * <b>Details: </b>A function call statement on a contracted function will
	 * be divided into two separate statements:
	 * <ul>
	 * <li>contracted_function_call_enter: An enter statement evaluates all
	 * parameters and pushes the call stack entry into the call stack.</li>
	 * 
	 * <li>contracted_function_call_exit: An exit statement may has guard
	 * specified by function contracts (e.g. waitsfor clauses). Requirements
	 * checking and assuming ensurances will happen during the execution of the
	 * exit statement. It pops the call stack, give the control back to the
	 * caller.</li>
	 * </ul>
	 * 
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param call
	 *            The call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeContractedFunctionCallEnter(State state, int pid,
			String process, ContractedFunctionCallStatement call)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] arguments;
		Evaluation eval;
		CIVLFunction function = call.function();

		// Evaluating arguments:
		arguments = new SymbolicExpression[call.arguments().size()];
		for (int i = 0; i < call.arguments().size(); i++) {
			eval = evaluator.evaluate(state, pid, call.arguments().get(i));

			state = eval.state;
			arguments[i] = eval.value;
		}
		state = stateFactory.pushCallStack(state, pid, function, arguments);
		return stateFactory.setLocation(state, pid, call.target());
	}

	// TODO: function.functionType parameterTypes may have bug!

	/**
	 * <p>
	 * <b>Summray: </b> Executes a contracted function call exit statement. This
	 * method pops the call stack and does reasoning on function contracts.
	 * </p>
	 * Details about function call enter and exit, see
	 * {@link #executeContractedFunctionCallEnter(State, int, String, ContractedFunctionCallStatement)}
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the current process.
	 * @param process
	 *            The String identifier of the process.
	 * @param call
	 *            The contracted function call statement.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeContractedFunctionCallExit(State state, int pid,
			String process, ContractedFunctionCallStatement call)
			throws UnsatisfiablePathConditionException {
		// Since a call on a contracted function does not execute the function
		// body, there is no accurate returned value. A canonical symbolic value
		// of a returned result from a function shall be an abstract function
		// call with parameters of the function.
		// TODO: Such a canonical value is correct under the assumption that the
		// called function is pure. A pure function should be replayable by
		// giving same parameters.
		SymbolicConstant tmpRetAbstractFunc;
		SymbolicExpression tmpRetVal;
		Variable result;
		CIVLFunction function = call.function();
		String functionName = function.name().name();
		List<SymbolicType> inputTypes = new LinkedList<>();
		SymbolicExpression[] arguments;
		int paramCounter = 0;

		// Evaluating arguments:
		arguments = new SymbolicExpression[call.arguments().size()];
		for (Variable param : function.parameters()) {
			int dyscopeId = state.getDyscopeID(pid, param);
			arguments[paramCounter++] = state.getVariableValue(dyscopeId,
					param.vid());

		}
		// Make returned value an uninterpreted expression (abstract function
		// call) :
		for (Variable arg : function.parameters())
			inputTypes.add(arg.type().getDynamicType(universe));
		tmpRetAbstractFunc = universe.symbolicConstant(universe
				.stringObject(function.name().name()), universe.functionType(
				inputTypes, function.returnType().getDynamicType(universe)));
		tmpRetVal = universe
				.apply(tmpRetAbstractFunc, Arrays.asList(arguments));
		result = function.outerScope().variable(
				ModelConfiguration.ContractResultName);
		state = result != null ? stateFactory.setVariable(state, result, pid,
				tmpRetVal) : state;
		// Checking requirements and assuming ensurances:
		state = inferByContracts(state, pid, process, functionName,
				function.functionContract());
		state = stateFactory.popCallStack(state, pid);
		// Assign returned value:
		state = call.lhs() != null ? assign(state, pid, process, call.lhs(),
				tmpRetVal) : state;
		return stateFactory.setLocation(state, pid, call.target());
	}

	/**
	 * <p>
	 * <b>Summary: </b> Executes a {@link ContractVerifyStatement}.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b> A {@link ContractVerifyStatement} stmt starts a
	 * procedure to do modular verification on the attached function f. All
	 * processes should be synchronized before stmt. A new state will be
	 * generated based on contracts of f in which all processes locate at the
	 * very beginning of the body of f. The verification procedure terminates
	 * when all processes return from f. Then the control returns to the next
	 * location of stmt.
	 * </p>
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param process
	 *            The String identifier of the process
	 * @param conVeri
	 *            The {@link ContractVerifyStatement}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeContractVerifyCall(State state, int pid,
			String process, ContractVerifyStatement conVeri)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] arguments;
		CIVLFunction function = conVeri.function();
		// Function identifier evaluation
		Triple<State, CIVLFunction, Integer> funcEval;
		Evaluation eval;
		int argCounter = 0;

		// Evaluating arguments:
		arguments = new SymbolicExpression[conVeri.arguments().size()];
		for (Expression argument : conVeri.arguments()) {
			eval = evaluator.evaluate(state, pid, argument);

			state = eval.state;
			arguments[argCounter++] = eval.value;
		}
		funcEval = evaluator.evaluateFunctionIdentifier(state, pid,
				conVeri.functionExpression(), conVeri.getSource());
		state = stateFactory.pushCallStack(state, pid, function,
				funcEval.third, arguments);
		state = enterContractVerifyState(state, pid, process, function);
		return state;
	}

	/*********
	 * Middle layer: semantics of contracts system execution
	 ***********/
	/**
	 * <p>
	 * <b>Summary: </b> Helper method. This method handles function contracts of
	 * a function f' when f' be called.
	 * </p>
	 * <p>
	 * <b>Details: Every time a contracted function f' is called, the change of
	 * states only depends on the contracts of f'. i.e. All requirements of f'
	 * must be satisfied immediately before the call and all ensurances of f'
	 * must be assumed immediately after the call.</b>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param functionName
	 *            The name of the function
	 * @param contract
	 *            The {@link FunctionContracts} of the function.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State inferByContracts(State state, int pid, String process,
			String functionName, FunctionContract contract)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehav;
		// Ensurances must be evaluated and assumed after all requirements are
		// checked, so it's efficient to cache them first when they are seen
		// then evaluates them after checking requirements:
		List<Expression> ensurancesFromValidNamedBehaviors = new LinkedList<>();

		defaultBehav = contract.defaultBehavior();
		// Verifies local requirements:
		state = verifyLocalContractClauses(state, pid, process, functionName,
				defaultBehav.requirements());
		for (MPICollectiveBehavior mpiCollective : contract.getMPIBehaviors()) {
			Reasoner reasoner = universe.reasoner(state.getPathCondition());

			// Verifies mpi requirements collectively:
			state = executeCollectiveContract(state, pid, process,
					mpiCollective.requirements(), mpiCollective.communicator(),
					null, ContractKind.INFER, mpiCollective.getSource());
			reasoner = universe.reasoner(state.getPathCondition());
			for (NamedFunctionBehavior namedBehav : mpiCollective
					.namedBehaviors()) {
				Evaluation eval;
				BooleanExpression assumptions;

				eval = evaluator.evaluate(state, pid, namedBehav.assumptions());
				state = eval.state;
				assumptions = (BooleanExpression) eval.value;
				if (reasoner.isValid(assumptions)) {
					state = executeCollectiveContract(state, pid, process,
							namedBehav.requirements(),
							mpiCollective.communicator(), null,
							ContractKind.INFER, namedBehav.getSource());
					for (Expression ensurance : namedBehav.ensurances())
						ensurancesFromValidNamedBehaviors.add(ensurance);
				}
			}
			// Assumes mpi ensurances collectively:
			for (Expression ensurance : mpiCollective.ensurances())
				ensurancesFromValidNamedBehaviors.add(ensurance);
			state = assumeWithPartialCollectiveEvaluation(state, pid, process,
					functionName, ensurancesFromValidNamedBehaviors,
					mpiCollective.communicator());
			state = executeCollectiveContract(state, pid, process,
					Arrays.asList(modelFactory.trueExpression(null)),
					mpiCollective.communicator(), null, ContractKind.WAITSFOR,
					mpiCollective.getSource());
		}
		// Assumes local ensurances:
		state = assumeLocalContractClauses(state, pid, process, functionName,
				defaultBehav.ensurances());
		return state;
	}

	/**
	 * <p>
	 * <b>Summary :</b> This is a helper method, it uses
	 * {@link ContractConditionGenerator} to generate a boolean expression based
	 * on given contract predicates. The result can be used to prove
	 * consequences of those contract predicates.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @param contracts
	 *            The function contracts
	 * @param names
	 *            Output argument: A container for valid behavior names.
	 * @return The boolean expression generated from given contracts
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression generateConditionsForContracts(State state,
			int pid, String process, CIVLFunction function,
			FunctionContract contracts)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehavior = contracts.defaultBehavior();
		BooleanExpression result;

		result = conditionGenerationWorker(state, pid, process,
				defaultBehavior.requirements());
		for (MPICollectiveBehavior mpiCollective : contracts.getMPIBehaviors()) {
			BooleanExpression subResult;

			// TODO: currently not checking emptyIObuffer because current design
			// guarantees such property, but it needs be checked eventually:
			subResult = conditionGenerationWorker(state, pid, process,
					mpiCollective.requirements());
			for (NamedFunctionBehavior namedBehavior : mpiCollective
					.namedBehaviors()) {
				Evaluation evaluation;
				BooleanExpression subsubResult;
				Reasoner reasoner;

				evaluation = evaluator.evaluate(state, pid,
						namedBehavior.assumptions());
				state = evaluation.state;
				reasoner = universe.reasoner(state.getPathCondition());
				if (reasoner.isValid((BooleanExpression) evaluation.value)) {
					subsubResult = conditionGenerationWorker(state, pid,
							process, namedBehavior.requirements());
					subResult = universe.and(subResult, subsubResult);
				}
			}
			result = universe.and(result, subResult);
		}
		return result;
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> Given expressions must have bool types.
	 * </p>
	 * <p>
	 * <b>Summary: </b> Helper method. Use {@link ContractConditionGenerator} to
	 * generate a boolean expression from a set of expressions. The generated
	 * boolean expression is the conjunction of the values of given expression
	 * set.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param conditions
	 *            A {@link Iterable} set of processes.
	 * @return Return the generated boolean expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression conditionGenerationWorker(State state, int pid,
			String process, Iterable<Expression> conditions)
			throws UnsatisfiablePathConditionException {
		BooleanExpression result = universe.trueExpression();
		boolean isFirst = true;

		for (Expression condition : conditions) {
			Evaluation eval = conditionGenerator.deriveExpression(state, pid,
					condition);

			state = eval.state;
			result = isFirst && (isFirst = false) == false ? (BooleanExpression) eval.value
					: universe.and(result, (BooleanExpression) eval.value);
		}
		return result;
	}

	/**
	 * <p>
	 * <b>Summary: </b>An helper method, this method should be called when a
	 * function f invoked by a {link ContractVerifyStatement} is returned. It
	 * checks if all ensurances of the function f holds.
	 * </p>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @param contracts
	 *            The function contracts
	 * @return The state after this checking.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State verifyContractsAtReturn(State state, int pid, String process,
			CIVLFunction function, FunctionContract contracts)
			throws UnsatisfiablePathConditionException {
		FunctionBehavior defaultBehavior = contracts.defaultBehavior();
		String functionName = function.name().name();

		// Verifies local ensurances:
		state = verifyLocalContractClauses(state, pid, process, functionName,
				defaultBehavior.ensurances());
		for (MPICollectiveBehavior mpiCollective : contracts.getMPIBehaviors()) {
			List<Expression> ensuredConditions = wildcardMPIEmptyIO(state, pid,
					process, mpiCollective, mpiCollective.getSource(), function);
			Reasoner reasoner = universe.reasoner(state.getPathCondition());

			for (Expression ensuredCondition : mpiCollective.ensurances())
				ensuredConditions.add(ensuredCondition);
			for (NamedFunctionBehavior namedBehav : mpiCollective
					.namedBehaviors()) {
				Evaluation evaluation;

				evaluation = evaluator.evaluate(state, pid,
						namedBehav.assumptions());
				state = evaluation.state;
				if (reasoner.isValid((BooleanExpression) evaluation.value))
					for (Expression ensuredCondition : namedBehav.ensurances())
						ensuredConditions.add(ensuredCondition);
			}
			state = executeCollectiveContract(state, pid, process,
					ensuredConditions, mpiCollective.communicator(), null,
					ContractKind.ENSURES, mpiCollective.getSource());
		}
		return state;
	}

	/**************** Contracted execution helper methods ********************/
	/*
	 * There are in total 4 execution situations in execution: 1. Enter the
	 * verifying function (ENTER VF); 2. Exit the verifying function (EXIT VF);
	 * 3. Call a contracted function (CALL CF); 4. Leave a contracted function
	 * (RETURN CF).
	 * 
	 * For all 4 cases, methods for assuming and checking local predicates are
	 * shared. All of them use {verifyLocalContractClauses} and
	 * {assumeLocalContractClauses}.
	 * 
	 * Case 1 only do assuming. Assuming global properties relies on
	 * synchronizations of all participating processes at the entry of VF (TODO:
	 * currently not implemented).
	 * 
	 * case 2 only do checking. Checking global properties relies on collective
	 * checking {executeCollectiveContracts}.
	 * 
	 * case 3 only do assuming. Assuming global properties is do partial
	 * collective evaluation on predicates, then add them to the path
	 * conditions.
	 * 
	 * case 4 only do checking. Checking global properties is do partial
	 * collective evaluation on predicates, then prove their satisfiability.
	 */
	/**
	 * <p>
	 * <b>Pre-condition: </b> "predicates" must all have bool types.
	 * </p>
	 * <p>
	 * <b>Summary: </b> Applies partial collective evaluation on a set of
	 * expressions.
	 * </p>
	 * 
	 * Details about partial collective evaluation can be found at
	 * {@link LibmpiEvaluator}.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param functionName
	 *            The String type function name
	 * @param predicates
	 *            A set of expressions which must have bool types
	 * @param mpiComm
	 *            An expression representing an MPI communicator
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State assumeWithPartialCollectiveEvaluation(State state, int pid,
			String process, String functionName,
			Iterable<Expression> predicates, Expression mpiComm)
			throws UnsatisfiablePathConditionException {
		Expression combinedPredicates = combinePredicates(state, pid, process,
				predicates);
		BooleanExpression newPathCondition;
		Evaluation eval;

		eval = evaluator.synchronizedEvaluate(state, pid, process,
				combinedPredicates, mpiComm);
		state = eval.state;
		newPathCondition = universe.and(state.getPathCondition(),
				(BooleanExpression) eval.value);
		return state.setPathCondition(newPathCondition);
	}

	/**
	 * <p>
	 * <b>Pre-condition :</b> "predicates" must all have bool types and they
	 * must only state local properties.
	 * </p>
	 * <p>
	 * <b>Summary :</b> Checks if a set of boolean expressions hold.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param process
	 *            The String identifier of the process
	 * @param functionName
	 *            The String type function name
	 * @param predicates
	 *            The set of expressions which must have bool types
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State verifyLocalContractClauses(State state, int pid,
			String process, String functionName, Iterable<Expression> predicates)
			throws UnsatisfiablePathConditionException {
		Reasoner reasoner;

		// Expressions have bool type
		for (Expression expression : predicates) {
			Evaluation eval = evaluator.evaluate(state, pid, expression);
			ResultType resultType;

			state = eval.state;
			reasoner = universe.reasoner(state.getPathCondition());
			resultType = reasoner.valid((BooleanExpression) eval.value)
					.getResultType();
			if (!resultType.equals(ResultType.YES)) {
				String message = "Contract condition : " + expression
						+ " is not satisfied when calling function "
						+ functionName;

				state = errorLogger.logError(expression.getSource(), state,
						process, symbolicAnalyzer.stateInformation(state),
						(BooleanExpression) eval.value, resultType,
						ErrorKind.CONTRACT, message);
			}
		}
		return state;
	}

	/**
	 * <p>
	 * <b>Pre-condition :</b> "predicates" must all have bool types and they
	 * must only state local properties.
	 * </p>
	 * <p>
	 * <b>Summary: </b> Evaluates a set of boolean expressions, adds their
	 * values into current path conditions
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The current PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param functionName
	 *            The String type function name
	 * @param predicates
	 *            The set of expression which must have bool types
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State assumeLocalContractClauses(State state, int pid,
			String process, String functionName, Iterable<Expression> predicates)
			throws UnsatisfiablePathConditionException {
		BooleanExpression context = state.getPathCondition();

		for (Expression condition : predicates) {
			Evaluation eval = evaluator.evaluate(state, pid, condition);

			state = eval.state;
			context = (BooleanExpression) universe.canonic(universe.and(
					context, (BooleanExpression) eval.value));
		}
		return state.setPathCondition(context);
	}

	/***************
	 * Low layer: (Partial) collective evaluation
	 ****************/

	/**
	 * <p>
	 * <b>Summary :</b> Executes collective algorithms for given contracts.
	 * </p>
	 * <p>
	 * <b>Details :</b> Details about collective algorithms can be found in
	 * {@link LibmpiExecutor}. A collective algorithm aims to evaluate some
	 * properties involving multiple processes in several steps.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param predicates
	 *            A set of expressions that will be evaluated collectively
	 * @param kind
	 *            {@link ContractKind} which denotes different snapsnot entries
	 * @param mpiComm
	 *            The MPI collective behavior block corresponding to this
	 *            execution.
	 * @param agreedVars
	 *            Optional: A set of agreed variables. Can be null if no agreed
	 *            variables.
	 * @param source
	 *            CIVLSource of the contracts
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeCollectiveContract(State state, int pid,
			String process, Iterable<Expression> predicates,
			Expression mpiComm, Variable[] agreedVars, ContractKind kind,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		Expression[] args = new Expression[2];
		LibmpiExecutor mpiExecutor;

		try {
			mpiExecutor = (LibmpiExecutor) loader.getLibraryExecutor("mpi",
					this, modelFactory, symbolicUtil, symbolicAnalyzer);
			args[0] = mpiComm;
			args[1] = combinePredicates(state, pid, process, predicates);
			return mpiExecutor.executeCollectiveEvaluation(state, pid, process,
					args, agreedVars, kind, source);
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library evaluator for the library ");
			message.append("mpi");
			message.append(" for the \\mpi_collective(...) contracts ");
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}

	/****************** Constructing Contract Start State ********************/
	/**
	 * This method is responsible for constructing an isolated start environment
	 * for a function invoked by a {@link ContractVerifyStatement}. The
	 * environment is built based on CIVL contract system semantics and the
	 * contracts of the function.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function
	 * @return The start state of the execution of the function body.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State enterContractVerifyState(State state, int pid,
			String process, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		// initialize all visible variables
		Scope outScope = function.outerScope().parent();
		Evaluation eval;
		Reasoner reasoner;

		// If the control got here, all involved processes are synchronized
		// here:
		while (outScope != null) {
			Variable[] variables = outScope.variables().clone();
			int dyscope = state.getDyscope(pid, outScope);

			// TODO: need a don't touch list
			// Don't initialize unreachable variables:
			if (state.reachableByProcess(dyscope, pid)) {
				for (Variable var : variables) {
					if (var.vid() != 0 && canIInitThisVariable(outScope, var)) {
						if (var.type().isPointerType()) {
							Expression initVar;

							var.setIsInput(true);
							initVar = modelFactory.initialValueExpression(
									var.getSource(), var);
							eval = evaluator.evaluate(state, pid, initVar);
							var.setIsInput(false);
						} else
							eval = evaluator.havoc(state, var.type()
									.getDynamicType(universe));
						state = eval.state;
						state = stateFactory.setVariable(state, var, pid,
								eval.value);
					}
				}
			}
			outScope = outScope.parent();
		}

		// Initialize pointer type parameters:
		Iterator<Variable> paraIter = function.parameters().iterator();

		while (paraIter.hasNext()) {
			Expression initVar;

			Variable para = paraIter.next();

			if (para.type().isPointerType()) {
				para.setIsInput(true);
				initVar = modelFactory.initialValueExpression(para.getSource(),
						para);
				eval = evaluator.evaluate(state, pid, initVar);
				para.setIsInput(false);
				state = eval.state;
				state = stateFactory.setVariable(state, para, pid, eval.value);
			}
		}
		// Set $mpi_sys_status to INITIALIZED it it exists:
		state = setMPISysStatusIfExists(state, pid, function.outerScope()
				.parent(), evaluator.INITIALIZED);
		/******* Necessary derivation on contracts *******/
		// PHASE 1: Derives contracts to reasonable boolean expressions:
		Iterator<Expression> requiresIter;
		BooleanExpression context;
		FunctionContract contracts = function.functionContract();
		List<Pair<PointerSetExpression, Integer>> validConsequences = new LinkedList<>();

		// deliver agreed variables
		for (MPICollectiveBehavior mpiCollective : contracts.getMPIBehaviors()) {
			state = executeCollectiveContract(state, pid, process,
					Arrays.asList(modelFactory.trueExpression(null)),
					mpiCollective.communicator(),
					mpiCollective.agreedVariables(), ContractKind.REQUIRES,
					mpiCollective.getSource());
		}
		context = generateConditionsForContracts(state, pid, process, function,
				contracts);
		// PHASE 2: Reasoning some clauses that need special handling:
		// TODO: reasoning is depend on process but current valid consequences
		// are not stored by PID
		for (Pair<Expression, Integer> guess : function
				.getPossibleValidConsequences()) {
			PointerSetExpression mem;

			eval = conditionGenerator.deriveExpression(state, pid, guess.left);
			state = (ImmutableState) eval.state;
			if (isRequirementConsequence(context,
					(BooleanExpression) eval.value)) {
				mem = (PointerSetExpression) ((UnaryExpression) guess.left)
						.operand();
				validConsequences.add(new Pair<>(mem, guess.right));
			}
		}
		state = state.setPathCondition(universe.and(context,
				state.getPathCondition()));
		// PHASE 2.1 Special handling on some clauses:
		conditionGenerator.setValidConsequences(validConsequences);
		state = concretizeAllPointers(state, pid, function, conditionGenerator);

		// PHASE 3: Evaluating contracts phase:
		context = state.getPathCondition();
		requiresIter = contracts.defaultBehavior().requirements().iterator();
		while (requiresIter.hasNext()) {
			BooleanExpression pred;
			Expression require = requiresIter.next();

			eval = evaluator.evaluate(state, pid, require);
			state = (ImmutableState) eval.state;
			reasoner = universe.reasoner(context);
			pred = (BooleanExpression) eval.value;
			context = universe.and(context, pred);
			if (reasoner.getReducedContext().isFalse()) {
				SymbolicAnalyzer symbolicAnalyzer = evaluator
						.symbolicAnalyzer();

				evaluator.errorLogger().logSimpleError(require.getSource(),
						state, process,
						symbolicAnalyzer.stateInformation(state),
						ErrorKind.CONTRACT,
						"Unsatisfiable requirements: " + require);
			}
		}
		state = state.setPathCondition(context);
		return state;
		// return stateFactory.canonic(state, false, false, false, null);
	}

	/*********************
	 * Miscellaneous helper methods
	 ************************/
	private boolean isRequirementConsequence(BooleanExpression context,
			BooleanExpression consequence) {
		Reasoner reasoner;

		reasoner = universe.reasoner(context);
		return reasoner.isValid(consequence);
	}

	/**
	 * <p>
	 * <b>Summary :</b> A helper method, it allocates memory spaces for all
	 * valid pointers.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param function
	 *            The {@link CIVLFunction} whose contracts denote those valid
	 *            pointers
	 * @param conditionGenerator
	 *            A reference to the {@link ContractConditionGenerator}, which
	 *            saves all valid pointers.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private ImmutableState concretizeAllPointers(State state, int pid,
			CIVLFunction function, ContractConditionGenerator conditionGenerator)
			throws UnsatisfiablePathConditionException {
		Iterator<List<Integer>> mallocsIter = conditionGenerator
				.validPointersIterator();
		String process = "p" + pid;
		Evaluation eval;

		while (mallocsIter.hasNext()) {
			List<Integer> mallocIDs = mallocsIter.next();
			Scope scope = function.outerScope();
			int dyscopeId = state.getDyscope(pid, scope);

			for (Integer i : mallocIDs) {
				MallocStatement mallocStmt = modelFactory.model().getMalloc(i);
				SymbolicExpression range;
				NumericExpression size;
				Pair<State, SymbolicExpression> ret;

				if (mallocStmt.getSizeExpression() != null) {
					eval = evaluator.evaluate(state, pid,
							mallocStmt.getSizeExpression());
					state = eval.state;
					range = eval.value;
					size = symbolicUtil.getHighOfRegularRange(range);
					// \valid(ptr + (0..n)) ==> there are (n + 1) objects in
					// heap:
					size = universe.add(size, universe.oneInt());
				} else
					size = universe.oneInt();
				ret = stateFactory.malloc(state, pid, dyscopeId, i,
						mallocStmt.getDynamicElementType(), size);
				state = ret.left;
				state = assign(state, pid, process, mallocStmt.getLHS(),
						ret.right);
			}
		}
		return (ImmutableState) state;
	}

	/**
	 * <p>
	 * <b>Summary: </b> A helper method, returns true if and only if a given
	 * variable is not a defined constant or a system variable which is
	 * invisible for programmers.
	 * </p>
	 * 
	 * @param scope
	 *            The scope where the variable is
	 * @param var
	 *            The given variable
	 * @return
	 */
	private boolean canIInitThisVariable(Scope scope, Variable var) {
		String varName = var.name().name();

		if (varName.startsWith("_"))
			return false;
		switch (varName) {
		case ModelConfiguration.GENERAL_ROOT:
			// case ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER:
			// case ModelConfiguration.SYMBOLIC_INPUT_COUNTER:
		case ModelConfiguration.ATOMIC_LOCK_VARIABLE:
		case ModelConfiguration.TIME_COUNT_VARIABLE:
		case ModelConfiguration.GCOMM_WORLD:
		case ModelConfiguration.GCOMMS:
		case ModelConfiguration.COMM_WORLD:
		case ModelConfiguration.MPI_SYS_STATUS:
		case ModelConfiguration.NPROCS:
		case ModelConfiguration.NPROCS_LOWER_BOUND:
		case ModelConfiguration.NPROCS_UPPER_BOUND:
		case ModelConfiguration.ContractMPICommRankName:
		case ModelConfiguration.ContractMPICommSizeName:
			return false;
		default:
			return true;
		}
	}

	/**
	 * <p>
	 * <b>Summary: </b>A helper method, Creates a list of wildcard \mpi_empty_in
	 * and \mpi_empty_out expressions for a {@link MPICollectiveBehavior}.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param mpiCollective
	 *            The MPI collective behavior block corresponding to these
	 *            expressions
	 * @param source
	 *            CIVLSource for these generated expressions
	 * @param function
	 *            The {@link CIVLFunction} corresponding to these expressions.
	 * @return
	 */
	private List<Expression> wildcardMPIEmptyIO(State state, int pid,
			String process, MPICollectiveBehavior mpiCollective,
			CIVLSource source, CIVLFunction function) {
		Expression[] argument = new Expression[1];
		List<Expression> result = new LinkedList<>();
		MPIContractExpression wildcard_mpiemptyIn = null;
		MPIContractExpression wildcard_mpiemptyOut = null;

		argument[0] = modelFactory.wildcardExpression(null, modelFactory
				.typeFactory().integerType());
		wildcard_mpiemptyIn = modelFactory.mpiContractExpression(source,
				function.outerScope(), mpiCollective.communicator(), argument,
				MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_IN,
				mpiCollective.mpiCommunicationPattern());
		wildcard_mpiemptyOut = modelFactory.mpiContractExpression(source,
				function.outerScope(), mpiCollective.communicator(), argument,
				MPI_CONTRACT_EXPRESSION_KIND.MPI_EMPTY_OUT,
				mpiCollective.mpiCommunicationPattern());
		result.add(wildcard_mpiemptyIn);
		result.add(wildcard_mpiemptyOut);
		return result;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Conjuncts a set of {@link Expression}s into a whole
	 * {@link BinaryExpression} whose operator is {@link BINARY_OPERATOR#AND}.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param predicates
	 *            The expression set which must have bool type.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Expression combinePredicates(State state, int pid, String process,
			Iterable<Expression> predicates)
			throws UnsatisfiablePathConditionException {
		boolean isFirst = true;
		Expression combinedPredicates = null;

		for (Expression predicate : predicates) {
			CIVLSource combinedSource = isFirst ? predicate.getSource()
					: modelFactory.sourceOfSpan(combinedPredicates.getSource(),
							predicate.getSource());

			// The conditional expression has side-effects which changes
			// "isFirst" to false once it's reached:
			combinedPredicates = isFirst && (isFirst = false) == false ? predicate
					: modelFactory.binaryExpression(combinedSource,
							BINARY_OPERATOR.AND, combinedPredicates, predicate);
		}
		return combinedPredicates != null ? combinedPredicates : modelFactory
				.trueExpression(null);
	}

	/**
	 * Set the system variable _mpi_sys_status_ with the given value "status" if
	 * the variable exists.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param scope
	 *            The Scope to start looking for such an variable
	 * @param status
	 *            The status value will be set to the variable.
	 * @return
	 */
	private State setMPISysStatusIfExists(State state, int pid, Scope scope,
			NumericExpression status) {
		while (scope != null) {
			Variable mpiSysStatus = scope
					.variable(ModelConfiguration.MPI_SYS_STATUS);

			if (mpiSysStatus != null) {
				state = stateFactory.setVariable(state, mpiSysStatus, pid,
						status);
				break;
			} else
				scope = scope.parent();
		}
		return state;
	}

}
