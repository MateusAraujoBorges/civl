package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractVerifyStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;

/**
 * CommonEnabler implements {@link EnablerIF} for CIVL models. It is an abstract
 * class and can have different implementations for different reduction
 * techniques.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public abstract class CommonEnabler implements Enabler {

	/* *************************** Instance Fields ************************* */

	/**
	 * Turn on/off debugging option to print more information.
	 */
	protected boolean debugging = false;

	/**
	 * The output stream for printing debugging information.
	 */
	protected PrintStream debugOut = System.out;

	/**
	 * The unique evaluator used by the system.
	 */
	protected Evaluator evaluator;

	/**
	 * The unique model factory used by the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The option to enable/disable the printing of ample sets of each state.
	 */
	protected boolean showAmpleSet = false;

	/**
	 * Show the impact/reachable memory units?
	 */
	protected boolean showMemoryUnits = false;

	/**
	 * If negative, ignore, otherwise an upper bound on the number of live
	 * processes.
	 */
	protected int procBound;

	/**
	 * The unique symbolic universe used by the system.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic expression for the boolean value false.
	 */
	protected BooleanExpression falseExpression;

	/**
	 * The library enabler loader.
	 */
	protected LibraryEnablerLoader libraryLoader;

	/**
	 * Show ample sets with the states?
	 */
	protected boolean showAmpleSetWtStates = false;

	/**
	 * The state factory that provides operations on states.
	 */
	protected StateFactory stateFactory;

	/**
	 * The error logger for reporting errors.
	 */
	protected CIVLErrorLogger errorLogger;

	/**
	 * The symbolic analyzer to be used.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	protected CIVLConfiguration config;

	private static final HashMap<Integer, Map<Statement, BooleanExpression>> EMPTY_STATEMENT_GUARD_MAP = new HashMap<Integer, Map<Statement, BooleanExpression>>(
			0);

	private ContractConditionGenerator conditionGenerator;

	/**
	 * CIVL configuration file, which is associated with the given command line.
	 */
	protected CIVLConfiguration civlConfig;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of Enabler, called by the constructors of the
	 * classes that implements Enabler.
	 * 
	 * @param transitionFactory
	 *            The transition factory to be used for composing new
	 *            transitions.
	 * @param evaluator
	 *            The evaluator to be used for evaluating expressions.
	 * @param executor
	 *            The executor to be used for computing the guard of system
	 *            functions.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param showAmpleSet
	 *            The option to enable or disable the printing of ample sets.
	 */
	protected CommonEnabler(StateFactory stateFactory, Evaluator evaluator,
			SymbolicAnalyzer symbolicAnalyzer, LibraryEnablerLoader libLoader,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig,
			ContractConditionGenerator conditionGenerator) {
		this.errorLogger = errorLogger;
		this.evaluator = evaluator;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.config = civlConfig;
		this.debugOut = civlConfig.out();
		this.debugging = civlConfig.debug();
		this.showAmpleSet = civlConfig.showAmpleSet()
				|| civlConfig.showAmpleSetWtStates();
		this.showAmpleSetWtStates = civlConfig.showAmpleSetWtStates();
		this.modelFactory = evaluator.modelFactory();
		this.universe = modelFactory.universe();
		falseExpression = universe.falseExpression();
		this.libraryLoader = libLoader;
		this.stateFactory = stateFactory;
		this.showMemoryUnits = civlConfig.showMemoryUnits();
		this.procBound = civlConfig.getProcBound();
		this.conditionGenerator = conditionGenerator;
		this.civlConfig = civlConfig;
	}

	/* ************************ Methods from EnablerIF ********************* */

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;

		if (state.getPathCondition().isFalse())
			// return empty set of transitions.
			return Semantics.newTransitionSequence(state, true);
		// return resumable atomic transitions.
		transitions = enabledAtomicTransitions(state);
		if (transitions == null)
			// return ample transitions.
			transitions = enabledTransitionsPOR(state);
		return transitions;
	}

	@Override
	public boolean debugging() {
		return debugging;
	}

	@Override
	public PrintStream getDebugOut() {
		return debugOut;
	}

	/* **************************** Public Methods ************************* */

	@Override
	public Evaluation getGuard(Statement statement, int pid, State state) {
		try {
			return evaluator.evaluate(state, pid, statement.guard());
		} catch (UnsatisfiablePathConditionException e) {
			return new Evaluation(state, this.falseExpression);
		}
	}

	@Override
	public boolean hasMultiple(TransitionSequence sequence) {
		return sequence.numRemoved() + sequence.size() > 1;
	}

	@Override
	public boolean hasNext(TransitionSequence transitionSequence) {
		return !transitionSequence.isEmpty();
	}

	@Override
	public Transition next(TransitionSequence transitionSequence) {
		return transitionSequence.remove();
	}

	@Override
	public int numRemoved(TransitionSequence sequence) {
		return sequence.numRemoved();
	}

	@Override
	public Transition peek(TransitionSequence transitionSequence) {
		return transitionSequence.peek();
	}

	@Override
	public void print(PrintStream out, TransitionSequence transitionSequence) {
	}

	@Override
	public void printFirstTransition(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void printRemaining(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void setDebugOut(PrintStream debugOut) {
		this.debugOut = debugOut;
	}

	@Override
	public void setDebugging(boolean debugging) {
		this.debugging = debugging;
	}

	@Override
	public State source(TransitionSequence transitionSequence) {
		return transitionSequence.state();
	}

	/* ************************ Package-private Methods ******************** */

	/**
	 * Obtain enabled transitions with partial order reduction. May have
	 * different implementation of POR algorithms.
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions computed by a certain POR approach.
	 */
	abstract TransitionSequence enabledTransitionsPOR(State state);

	TransitionSequence enabledTransitionsOfAllProcesses(State state) {
		Iterable<? extends ProcessState> processes = state.getProcessStates();
		List<Transition> transitions = new LinkedList<>();
		TransitionSequence result = Semantics
				.newTransitionSequence(state, true);

		for (ProcessState process : processes) {
			transitions.addAll(this.enabledTransitionsOfProcess(state,
					process.getPid()));
		}
		result.addAll(transitions);
		return result;
	}

	/**
	 * Gets the enabled transitions of a certain process at a given state.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param pid
	 *            The process id to work with.
	 * @param newGuardMap
	 *            A map of process IDs and their guards of statements. This is
	 *            to reuse evaluation result of guards and it could be an empty
	 *            map if there is nothing to be reused.
	 * @return the list of enabled transitions of the given process at the
	 *         specified state
	 */
	List<Transition> enabledTransitionsOfProcess(State state, int pid,
			Map<Integer, Map<Statement, BooleanExpression>> newGuardMap) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		LinkedList<Transition> transitions = new LinkedList<>();
		int numOutgoing;
		AtomicLockAction atomicLockAction = AtomicLockAction.NONE;

		if (pLocation == null)
			return transitions;
		if (stateFactory.processInAtomic(state) != pid && p.atomicCount() > 0) {
			atomicLockAction = AtomicLockAction.GRAB;
		}
		numOutgoing = pLocation.getNumOutgoing();
		for (int i = 0; i < numOutgoing; i++) {
			Statement statement = pLocation.getOutgoing(i);
			BooleanExpression newPathCondition = newPathCondition(state, pid,
					statement, newGuardMap);

			if (!newPathCondition.isFalse()) {
				transitions.addAll(enabledTransitionsOfStatement(state,
						statement, newPathCondition, pid, atomicLockAction));
			}
		}
		return transitions;
	}

	LibraryEnabler libraryEnabler(CIVLSource civlSource, String library)
			throws LibraryLoaderException {
		return this.libraryLoader.getLibraryEnabler(library, this, evaluator,
				evaluator.modelFactory(), evaluator.symbolicUtility(),
				this.symbolicAnalyzer);
	}

	/* **************************** Private Methods ************************ */

	/**
	 * Computes transitions from the process owning the atomic lock or triggered
	 * by resuming an atomic block that is previously blocked. Adds an
	 * assignment to update atomic lock variable (i.e., grabbing the atomic
	 * lock) with the transition obtained by the statements.
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions that resume an atomic block.
	 */
	private TransitionSequence enabledAtomicTransitions(State state) {
		int pidInAtomic;

		pidInAtomic = stateFactory.processInAtomic(state);
		if (pidInAtomic >= 0) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = Semantics
					.newTransitionSequence(state, false);

			localTransitions.addAll(enabledTransitionsOfProcess(state,
					pidInAtomic, EMPTY_STATEMENT_GUARD_MAP));
			if (!localTransitions.isEmpty())
				return localTransitions;
		}
		return null;
	}

	/**
	 * Get the enabled transitions of a statement at a certain state. An
	 * assignment to the atomic lock variable might be forced to the returned
	 * transitions, when the process is going to re-obtain the atomic lock
	 * variable.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param s
	 *            The statement to be used to generate transitions.
	 * @param pathCondition
	 *            The current path condition.
	 * @param pid
	 *            The process id that the statement belongs to.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return The set of enabled transitions.
	 */
	private List<Transition> enabledTransitionsOfStatement(State state,
			Statement statement, BooleanExpression pathCondition, int pid,
			AtomicLockAction atomicLockAction) {
		List<Transition> localTransitions = new LinkedList<>();
		int processIdentifier = state.getProcessState(pid).identifier();

		try {
			if (statement instanceof CallOrSpawnStatement) {
				CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

				if (call.isSystemCall()) { // TODO check function pointer
					return this.getEnabledTransitionsOfSystemCall(
							call.getSource(), state, call, pathCondition, pid,
							processIdentifier, atomicLockAction);
				} else if (procBound > 0 && call.isSpawn()
						&& state.numLiveProcs() >= procBound) {
					// empty set: spawn is disabled due to procBound
					return localTransitions;
				}
			}
			if (statement instanceof ContractVerifyStatement) {
				if (!((ContractVerifyStatement) statement).isWorker())
					return this.enabledTransitionsOfContractVerifyStatement(
							state, (ContractVerifyStatement) statement,
							pathCondition, pid, processIdentifier,
							atomicLockAction);
			}
			localTransitions.add(Semantics.newTransition(pathCondition, pid,
					processIdentifier, statement, atomicLockAction));
		} catch (UnsatisfiablePathConditionException e) {
			// nothing to do: don't add this transition
		}
		return localTransitions;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Enable transitions right after a $contractVerify
	 * statement. Followings are situations that may need explore all possible
	 * transitions:
	 * <ul>
	 * <li>Elaborate free symbolic constants in behavior assumptions. (done)</li>
	 * <li>Enable transitions for each behavior. (not started)</li>
	 * <li>Pointer lazy initialization .(not started)</li>
	 * </ul>
	 * </p>
	 *
	 * @param state
	 *            The current state
	 * @param statement
	 *            The {@link ContractVerifyStatement}
	 * @param pathCondition
	 *            Current path condition
	 * @param pid
	 *            The PID of the process
	 * @param processIdentifier
	 *            The String identifier of the process
	 * @param atomicLockAction
	 *            The {@link AtomicLockAction}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public List<Transition> enabledTransitionsOfContractVerifyStatement(
			State state, ContractVerifyStatement statement,
			BooleanExpression pathCondition, int pid, int processIdentifier,
			AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		List<Transition> transitions = new LinkedList<>();
		List<BooleanExpression> newPCs = this
				.elaboratesAssumptions4ContractVerify(state, statement,
						pathCondition, pid, processIdentifier, atomicLockAction);
		// TODO: make each behavior deterministic
		// TODO: pointer lazy initialization
		// Creates ContractVerifyStatement workers:
		Location newSource = modelFactory.location(statement.getSource(),
				statement.statementScope());
		ContractVerifyStatement worker = modelFactory.contractVerifyStatement(
				statement.getSource(), statement.statementScope(), newSource,
				statement.functionExpression(), statement.arguments());

		worker.setAsWorker();
		for (BooleanExpression newPC : newPCs)
			transitions.add(Semantics.newTransition(newPC, pid,
					processIdentifier, worker, atomicLockAction));
		return transitions;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Returns a set of path conditions by elaborating all
	 * assumptions. Here elaborating a assumption means elaborating all possible
	 * values of each free symbolic constant in the assumption.
	 * </p>
	 * <p>
	 * <b>Details: </b> The elaboration procedure can be divided into two phase:
	 * 1. Elaborating assumptions in default behavior; 2. Elaborating
	 * assumptions in MPI collective behaviors. Note that phase 2 depends on
	 * phase 1, i.e. phase 2 is elaborating assumptions with each new path
	 * condition generated in phase 1.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param statement
	 *            The {@link ContractVerifyStatement}
	 * @param pathCondition
	 *            The current path condition
	 * @param pid
	 *            The PID of the process
	 * @param processIdentifier
	 *            The String identifier of the process
	 * @param atomicLockAction
	 *            The {@link AtomicLockAction}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<BooleanExpression> elaboratesAssumptions4ContractVerify(
			State state, ContractVerifyStatement statement,
			BooleanExpression pathCondition, int pid, int processIdentifier,
			AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		CIVLFunction verifyingFunction = statement.function();
		Evaluation eval;
		State dummyState;
		BooleanExpression context = pathCondition;
		SymbolicExpression arguments[] = new SymbolicExpression[statement
				.arguments().size()];
		// Two path condition collections so that they can be used in turns:
		List<BooleanExpression> pathConds = new LinkedList<>();
		List<BooleanExpression> anotherPCs = new LinkedList<>();
		Set<SymbolicConstant> elaborateSet = new HashSet<>();
		int count = 0;

		// Push call entry to make a dummy state:
		for (Expression argument : statement.arguments()) {
			eval = evaluator.evaluate(state, pid, argument);
			state = eval.state;
			arguments[count++] = eval.value;
		}
		dummyState = stateFactory.pushCallStack(state, pid, verifyingFunction,
				arguments);
		// For each defaultBehavior or MPICollectiveBehavior, collect free
		// symbolic constants from assumptions first, then do intersection with
		// free symbolic constants in requirement expressions. With such a
		// strategy, if there is no NamedBehaviors in contracts, there is no
		// need to explore free symbolic constants.
		for (NamedFunctionBehavior namedBehavior : verifyingFunction
				.functionContract().namedBehaviors())
			elaborateSet.addAll(getFreeSymbolicConstantFromAssumption(
					dummyState, pid, namedBehavior));
		context = retainSymbolicConstantWithRequirements(dummyState, pid,
				elaborateSet, verifyingFunction.functionContract()
						.defaultBehavior());
		pathConds = elaboratePathConditionsWithFreeSymbolicConstants(context,
				elaborateSet, pathCondition);
		// MPI collective blocks
		elaborateSet.clear();
		for (BooleanExpression pathCond : pathConds)
			for (MPICollectiveBehavior collective : verifyingFunction
					.functionContract().getMPIBehaviors()) {
				for (NamedFunctionBehavior nameBehav : collective
						.namedBehaviors())
					elaborateSet.addAll(getFreeSymbolicConstantFromAssumption(
							dummyState, pid, nameBehav));
				context = retainSymbolicConstantWithRequirements(dummyState,
						pid, elaborateSet, collective);
				anotherPCs
						.addAll(elaboratePathConditionsWithFreeSymbolicConstants(
								context, elaborateSet, pathCond));
			}
		return anotherPCs.isEmpty() ? pathConds : anotherPCs;
	}

	/**
	 * Computes the set of enabled transitions of a system function call.
	 * 
	 * @param source
	 * @param state
	 * @param call
	 * @param pathCondition
	 * @param pid
	 * @param processIdentifier
	 * @param assignAtomicLock
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<Transition> getEnabledTransitionsOfSystemCall(
			CIVLSource source, State state, CallOrSpawnStatement call,
			BooleanExpression pathCondition, int pid, int processIdentifier,
			AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		SystemFunction sysFunction = (SystemFunction) call.function();
		String libraryName = sysFunction.getLibrary();

		if (sysFunction.needsEnabler()) {
			try {
				LibraryEnabler libEnabler = libraryEnabler(source, libraryName);

				return libEnabler
						.enabledTransitions(state, call, pathCondition, pid,
								processIdentifier, atomicLockAction);
			} catch (LibraryLoaderException exception) {
				return makeTransitions(pathCondition, pid, processIdentifier,
						atomicLockAction, call);
			}
		} else {
			return makeTransitions(pathCondition, pid, processIdentifier,
					atomicLockAction, call);
		}
	}

	/**
	 *
	 * @param pathCondition
	 * @param pid
	 * @param processIdentifier
	 * @param atomicLockAction
	 * @param call
	 * @return
	 */
	private List<Transition> makeTransitions(BooleanExpression pathCondition,
			int pid, int processIdentifier, AtomicLockAction atomicLockAction,
			CallOrSpawnStatement call) {
		List<Transition> localTransitions = new LinkedList<>();

		localTransitions.add(Semantics.newTransition(pathCondition, pid,
				processIdentifier, call, atomicLockAction));
		return localTransitions;
	}

	/**
	 * Given a state, a process, and a statement, check if the statement's guard
	 * is satisfiable under the path condition. If it is, return the conjunction
	 * of the path condition and the guard. This will be the new path condition.
	 * Otherwise, return false.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The id of the currently executing process.
	 * @param statement
	 *            The statement.
	 * @param newGuardMap
	 * @return The new path condition. False if the guard is not satisfiable
	 *         under the path condition.
	 */
	private BooleanExpression newPathCondition(State state, int pid,
			Statement statement,
			Map<Integer, Map<Statement, BooleanExpression>> newGuardMap) {
		BooleanExpression guard = null;
		Map<Statement, BooleanExpression> myMap = newGuardMap.get(pid);

		if (myMap != null)
			guard = myMap.get(statement);
		if (guard == null) {
			Evaluation eval = getGuard(statement, pid, state);

			guard = (BooleanExpression) eval.value;
		}
		if (guard.isFalse())
			return this.falseExpression;

		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (guard.isTrue()) {
			return pathCondition;
		}
		guard = (BooleanExpression) universe.canonic(guard);
		if (reasoner.isValid(universe.not(guard)))
			return this.falseExpression;
		if (reasoner.isValid(guard))
			return pathCondition;
		return (BooleanExpression) universe.canonic(universe.and(pathCondition,
				guard));
	}

	public List<Transition> enabledTransitionsOfProcess(State state, int pid) {
		return this.enabledTransitionsOfProcess(state, pid,
				new HashMap<Integer, Map<Statement, BooleanExpression>>(0));
	}

	/* ********************* Private helper method ************************* */
	// TODO: some method can be shared with LibcivlcEnabler for $elaborate.
	/**
	 * <p>
	 * <b>Summary: </b> Given an old path condition and a set of free symbolic
	 * constants, elaborate all possible values for each symbolic constant,
	 * returns a set of new path conditions.
	 * </p>
	 * 
	 * @param context
	 *            The context for inferring possible values for symbolic
	 *            constants.
	 * @param elaborateSet
	 *            The free symbolic constants set.
	 * @param pathCondition
	 *            The old path condition
	 * @return
	 */
	private List<BooleanExpression> elaboratePathConditionsWithFreeSymbolicConstants(
			BooleanExpression context, Set<SymbolicConstant> elaborateSet,
			BooleanExpression pathCondition) {
		List<BooleanExpression> newPCs = new LinkedList<>();

		if (elaborateSet.isEmpty()) {
			newPCs.add(pathCondition);
			return newPCs;
		}

		// Reasoning the possible interval:
		Reasoner reasoner = universe.reasoner(context);

		// Elaborates the elaborateSet:
		for (SymbolicConstant symConst : elaborateSet) {
			Interval interval = reasoner
					.intervalApproximation((NumericSymbolicConstant) symConst);

			if (interval != null) {
				Number lowerNum = interval.lower();
				Number upperNum = interval.upper();
				int lower, upper;

				if (lowerNum != null && upperNum != null) {
					BooleanExpression[] clauses;

					assert !interval.strictLower();
					assert !interval.strictUpper();
					lower = ((IntegerNumber) lowerNum).intValue();
					upper = ((IntegerNumber) upperNum).intValue();
					clauses = generateElaborateConditions(symConst, lower,
							upper);
					for (BooleanExpression clause : clauses)
						newPCs.add(universe.and(pathCondition, clause));
				}
			}
		}
		if (newPCs.isEmpty())
			newPCs.add(pathCondition);
		return newPCs;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Given a {@link FunctionBehavior} and a set of free
	 * symbolic constant s0. All free symbolic constants appears in requirements
	 * of the FunctionBehavior forms set s1. The elaborateSet will be updated to
	 * the intersection of s0 and s1. This method returns the conjunction of
	 * requirements of the FunctionBehavior.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param elaborateSet
	 *            The Free Symbolic Constant Set
	 * @param behavior
	 *            The {@link FunctionBehavior}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression retainSymbolicConstantWithRequirements(
			State state, int pid, Set<SymbolicConstant> elaborateSet,
			FunctionBehavior behavior)
			throws UnsatisfiablePathConditionException {
		if (elaborateSet.isEmpty())
			return universe.trueExpression();

		Set<SymbolicConstant> symConsts = new HashSet<>();
		BooleanExpression context = universe.trueExpression();

		for (Expression assumption : behavior.requirements()) {
			Evaluation eval = conditionGenerator.deriveExpression(state, pid,
					assumption);

			state = eval.state;
			symConsts.addAll(universe.getFreeSymbolicConstants(eval.value));
			context = universe.and(context, (BooleanExpression) eval.value);
		}
		elaborateSet.retainAll(symConsts);
		return context;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Given an {@link NamedFunctionBehavior}, returns all free
	 * symbolic constants appears in the assumptions of the
	 * NamedFunctionBehavior
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            Thd PID of the process
	 * @param behavior
	 *            The {@link NamedFunctionBehavior}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Set<SymbolicConstant> getFreeSymbolicConstantFromAssumption(
			State state, int pid, NamedFunctionBehavior behavior)
			throws UnsatisfiablePathConditionException {
		Set<SymbolicConstant> symConsts = new HashSet<>();
		Evaluation eval = conditionGenerator.deriveExpression(state, pid,
				behavior.assumptions());

		state = eval.state;
		symConsts.addAll(universe.getFreeSymbolicConstants(eval.value));
		return symConsts;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Given a symbolic constant a, a lower bound l and a
	 * higher bound h, this method returns a set of boolean expressions:
	 * </p>
	 * a == l, a == l + 1, ... a == h
	 * 
	 * @param var
	 *            The symbolic constant
	 * @param lower
	 *            The lower bound
	 * @param upper
	 *            The higher bound
	 * @return
	 */
	private BooleanExpression[] generateElaborateConditions(
			SymbolicConstant var, int lower, int upper) {
		assert lower <= upper;
		BooleanExpression result[] = new BooleanExpression[upper - lower + 1];

		result[0] = universe.equals(var, universe.integer(lower));
		for (int i = lower + 1; i <= upper; i++) {
			result[upper - i + 1] = universe.equals(var, universe.integer(i));
		}
		return result;
	}
}
