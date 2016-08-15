package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.statement.UpdateStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.WithStatement;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
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
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

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

	private Executor executor;

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

	/**
	 * CIVL configuration file, which is associated with the given command line.
	 */
	protected CIVLConfiguration civlConfig;

	private CollateExecutor collateExecutor;

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
			Executor executor, SymbolicAnalyzer symbolicAnalyzer,
			LibraryEnablerLoader libLoader, CIVLErrorLogger errorLogger,
			CIVLConfiguration civlConfig) {
		this.errorLogger = errorLogger;
		this.evaluator = evaluator;
		this.executor = executor;
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
		this.civlConfig = civlConfig;
		collateExecutor = new CollateExecutor(this, this.executor, errorLogger,
				civlConfig);
	}

	/* ************************ Methods from EnablerIF ********************* */

	@Override
	public TransitionSequence enabledTransitions(State state) {
		Pair<BooleanExpression, TransitionSequence> transitionsAssumption;
		TransitionSequence transitions = Semantics.newTransitionSequence(state,
				false);

		if (state.getPathCondition().isFalse())
			// return empty set of transitions.
			return Semantics.newTransitionSequence(state, true);
		// return resumable atomic transitions.
		transitionsAssumption = enabledAtomicTransitions(state);
		if (transitionsAssumption != null && transitionsAssumption.left != null)
			state = state.setPathCondition((BooleanExpression) universe
					.canonic(universe.and(state.getPathCondition(),
							transitionsAssumption.left)));
		if (transitionsAssumption != null
				&& transitionsAssumption.right != null)
			transitions.addAll(transitionsAssumption.right.transitions());
		if (transitionsAssumption == null || transitionsAssumption.right == null
				|| transitionsAssumption.left != null) {
			// return ample transitions.
			transitions.addAll(enabledTransitionsPOR(state).transitions());
		}
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
	public BooleanExpression getGuard(Statement statement, int pid,
			State state) {
		Evaluation eval;

		try {
			// TODO think about errors as side effects in the evaluator
			// Reasoner reasoner = universe.reasoner(universe.trueExpression());
			// BooleanExpression pcUnchanged;
			//
			eval = evaluator.evaluate(state, pid, statement.guard());
			// pcUnchanged = universe.equals(state.getPathCondition(),
			// eval.state.getPathCondition());
			// if (pcUnchanged.isTrue() || reasoner.isValid(pcUnchanged))
			// return (BooleanExpression) eval.value;
			return (BooleanExpression) eval.value;
		} catch (UnsatisfiablePathConditionException ex) {
			return universe.falseExpression();
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
	public void printFirstTransition(PrintStream arg0,
			TransitionSequence arg1) {
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

	List<Transition> enabledTransitionsOfProcess(State state, int pid) {
		return this.enabledTransitionsOfProcess(state, pid, null);
	}

	TransitionSequence enabledTransitionsOfAllProcesses(State state) {
		Iterable<? extends ProcessState> processes = state.getProcessStates();
		List<Transition> transitions = new LinkedList<>();
		TransitionSequence result = Semantics.newTransitionSequence(state,
				true);

		for (ProcessState process : processes) {
			transitions.addAll(
					this.enabledTransitionsOfProcess(state, process.getPid()));
		}
		result.addAll(transitions);
		return result;
	}

	/**
	 * Gets the enabled transitions of a certain process at a given state. It's
	 * possible that the atomic lock is free or another process is holding the
	 * atomic lock. TODO clarify situations for atomic
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
			BooleanExpression newGuardMap[][]) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		LinkedList<Transition> transitions = new LinkedList<>();
		AtomicLockAction atomicLockAction = AtomicLockAction.NONE;

		if (pLocation == null || pLocation.isSleep())
			return transitions;
		if (stateFactory.processInAtomic(state) != pid && p.atomicCount() > 0) {
			atomicLockAction = AtomicLockAction.GRAB;
		}
		if (pLocation.isBinaryBranching())
			return enabledTransitionsAtBinaryBranchingLocation(state, pLocation,
					pid, atomicLockAction);
		else
			return enabledTransitionsAtLocation(state, pLocation, pid,
					atomicLockAction, newGuardMap);
	}

	LibraryEnabler libraryEnabler(CIVLSource civlSource, String library)
			throws LibraryLoaderException {
		return this.libraryLoader.getLibraryEnabler(library, this, evaluator,
				evaluator.modelFactory(), evaluator.symbolicUtility(),
				this.symbolicAnalyzer);
	}

	/**
	 * generates enabled transitions for a given process at a certain location
	 * at the specified state
	 * 
	 * @param state
	 *            the current state
	 * @param pLocation
	 *            the location where the given process locates currently, which
	 *            should be consistent with the given state
	 * @param pid
	 *            the PID of the process
	 * @param atomicLockAction
	 *            the atomic lock action, either NONE or GRAB.
	 * @param newGuardMap
	 *            a map (could be empty) of process IDs and their guards of
	 *            statements. This is to reuse evaluation result of guards and
	 *            it could be an empty map if there is nothing to be reused.
	 * @return the list of transitions that are enabled for the given process at
	 *         the current state
	 */
	private List<Transition> enabledTransitionsAtLocation(State state,
			Location pLocation, int pid, AtomicLockAction atomicLockAction,
			BooleanExpression newGuardMap[][]) {
		int numOutgoing = pLocation.getNumOutgoing();
		LinkedList<Transition> transitions = new LinkedList<>();

		for (int i = 0; i < numOutgoing; i++) {
			Statement statement = pLocation.getOutgoing(i);
			BooleanExpression newPathCondition = newPathCondition(state, pid,
					statement, i, newGuardMap);

			if (!newPathCondition.isFalse()) {
				transitions.addAll(enabledTransitionsOfStatement(state,
						statement, newPathCondition, pid, atomicLockAction));
			}
		}
		return transitions;
	}

	/**
	 * generates enabled transitions for a given process at a binary branching
	 * location at the specified state. <br>
	 * Precondition: the process is at a binary branching location at the
	 * current state
	 * 
	 * @param state
	 *            the current state
	 * @param pLocation
	 *            the location where the given process locates currently, which
	 *            should be consistent with the given state
	 * @param pid
	 *            the PID of the process
	 * @param atomicLockAction
	 *            the atomic lock action, either NONE or GRAB.
	 * @return the list of transitions that are enabled for the given process at
	 *         the current state
	 */
	private List<Transition> enabledTransitionsAtBinaryBranchingLocation(
			State state, Location pLocation, int pid,
			AtomicLockAction atomicLockAction) {
		assert pLocation.isBinaryBranching();

		Statement first = pLocation.getOutgoing(0),
				second = pLocation.getOutgoing(1);
		BooleanExpression firstGuard = (BooleanExpression) this.getGuard(first,
				pid, state);
		BooleanExpression firstPc = null, secondPc = null;
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		LinkedList<Transition> transitions = new LinkedList<>();

		if (!firstGuard.isFalse()) {
			if (firstGuard.isTrue())
				firstPc = pathCondition;
			else {
				firstGuard = (BooleanExpression) universe.canonic(firstGuard);

				BooleanExpression notFirstGuard = (BooleanExpression) universe
						.canonic(universe.not(firstGuard));

				if (reasoner.isValid(notFirstGuard)) {
					secondPc = pathCondition;
				} else {
					if (reasoner.isValid(firstGuard))
						firstPc = pathCondition;
					else {
						firstPc = (BooleanExpression) universe.canonic(
								universe.and(pathCondition, firstGuard));
						secondPc = (BooleanExpression) universe.canonic(
								universe.and(pathCondition, notFirstGuard));
					}
				}
			}
		} else
			// firstGuard is false, then second guard is true
			secondPc = pathCondition;
		if (firstPc != null)
			transitions.addAll(enabledTransitionsOfStatement(state, first,
					firstPc, pid, atomicLockAction));
		if (secondPc != null)
			transitions.addAll(enabledTransitionsOfStatement(state, second,
					secondPc, pid, atomicLockAction));
		return transitions;
	}

	/* **************************** Private Methods ************************ */

	/**
	 * Computes transitions from the process owning the atomic lock or triggered
	 * by resuming an atomic block that is previously blocked. Adds an
	 * assignment to update atomic lock variable (i.e., grabbing the atomic
	 * lock) with the transition obtained by the statements. When the the
	 * process in atomic session is at a guarded location (where exact one
	 * statement is enabled with a non-trivial guard), then other processes
	 * needs to be considered with the assumption that the process in atomic
	 * session is blocked.
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions that resume an atomic block by a certain
	 *         process, and an optional boolean expression representing the
	 *         condition when the process in atomic is blocked.
	 */
	private Pair<BooleanExpression, TransitionSequence> enabledAtomicTransitions(
			State state) {
		int pidInAtomic;

		pidInAtomic = stateFactory.processInAtomic(state);
		if (pidInAtomic >= 0) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = Semantics
					.newTransitionSequence(state, false);
			Location location = state.getProcessState(pidInAtomic)
					.getLocation();

			if (location.isGuardedLocation()) {
				Statement statement = location.getOutgoing(0);
				BooleanExpression guardValue = this.getGuard(statement,
						pidInAtomic, state);
				BooleanExpression otherAssumption = null;
				BooleanExpression newPathCondition = state.getPathCondition();

				if (!guardValue.isFalse()) {
					if (!guardValue.isTrue()) {
						Reasoner reasoner = universe
								.reasoner(state.getPathCondition());

						BooleanExpression notGuard = (BooleanExpression) universe
								.canonic(universe.not(guardValue));

						if (reasoner.isValid(notGuard)) {
							return null;
						}
						if (!reasoner.isValid(guardValue)) {
							otherAssumption = notGuard;
							newPathCondition = (BooleanExpression) universe
									.canonic(universe.and(newPathCondition,
											guardValue));
						}
					}
					localTransitions.addAll(enabledTransitionsOfStatement(state,
							statement, newPathCondition, pidInAtomic,
							AtomicLockAction.NONE));
				}
				return new Pair<>(otherAssumption, localTransitions);
			} else {
				localTransitions.addAll(
						enabledTransitionsOfProcess(state, pidInAtomic, null));
			}
			if (!localTransitions.isEmpty())
				return new Pair<>(null, localTransitions);
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

		try {
			StatementKind kind = statement.statementKind();

			switch (kind) {
				case CALL_OR_SPAWN : {
					CallOrSpawnStatement call = (CallOrSpawnStatement) statement;

					if (call.isSystemCall()) { // TODO check function pointer
						return this.getEnabledTransitionsOfSystemCall(
								call.getSource(), state, call, pathCondition,
								pid, atomicLockAction);
					} else if (procBound > 0 && call.isSpawn()
							&& state.numLiveProcs() >= procBound) {
						// empty set: spawn is disabled due to procBound
						return localTransitions;
					}
					break;
				}
				case WITH :
					return enabledTransitionsOfWithStatement(state, pid,
							(WithStatement) statement, atomicLockAction);
				case UPDATE :
					return enabledTransitionsOfUpdateStatement(state, pid,
							(UpdateStatement) statement, atomicLockAction);
				default :
			}
			localTransitions.add(Semantics.newTransition(pathCondition, pid,
					statement, atomicLockAction));
		} catch (UnsatisfiablePathConditionException e) {
			// nothing to do: don't add this transition
		}
		return localTransitions;
	}

	/**
	 * prepares the appropriate collate state, and invokes the
	 * colExecutor.run2Completion() to run a sub-program, which returns a number
	 * of collate states.
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the current PID
	 * @param with
	 *            the with statement
	 * @return a list of transitions, each of which has the form
	 *         col_state.gstate->state=state_ID;
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<Transition> enabledTransitionsOfWithStatement(State state,
			int pid, WithStatement with, AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		Expression colStateExpr = with.collateState();
		CIVLSource csSource = colStateExpr.getSource();
		Evaluation eval;
		SymbolicExpression colStateComp, gstateHandle;
		int place, colStateID;
		SymbolicUtility symbolicUtil = evaluator.symbolicUtility();
		State colState;
		Collection<State> newColStates;
		LHSExpression colStateRef = modelFactory.dotExpression(csSource,
				modelFactory.dereferenceExpression(csSource,
						modelFactory.dotExpression(csSource, colStateExpr, 1)),
				1);
		BooleanExpression oldPC = state.getPathCondition();

		eval = this.evaluator.evaluate(state, pid, colStateExpr);
		state = eval.state;
		colStateComp = eval.value;
		place = symbolicUtil.extractInt(csSource, (NumericExpression) universe
				.tupleRead(colStateComp, universe.intObject(0)));
		gstateHandle = universe.tupleRead(colStateComp, universe.intObject(1));
		eval = this.evaluator.dereference(csSource, state, "p" + pid,
				colStateExpr, gstateHandle, false);
		state = eval.state;
		colStateID = this.modelFactory.getStateRef(csSource,
				universe.tupleRead(eval.value, universe.intObject(1)));
		colState = stateFactory.getStateByReference(colStateID);
		colState = stateFactory.addExternalProcess(colState, state, pid, place,
				with.function(), new SymbolicExpression[0]);
		newColStates = collateExecutor.run2Completion(state, pid, colState,
				this.civlConfig);
		return getCollateStateUpdateTransitions(oldPC, pid, colStateRef,
				newColStates, atomicLockAction, with);
	}

	private List<Transition> getCollateStateUpdateTransitions(
			BooleanExpression oldPC, int pid, LHSExpression colStateRef,
			Collection<State> colStates, AtomicLockAction atomicLockAction,
			Statement originalStmt) {
		List<Transition> result = new LinkedList<>();
		AssignStatement assign;
		CIVLSource csSource = colStateRef.getSource();

		for (State newColState : colStates) {
			Pair<Integer, State> newStateAndID = stateFactory
					.saveState(newColState, pid);

			// System.out.println(
			// this.symbolicAnalyzer.stateToString(newStateAndID.right));
			assign = modelFactory.assignStatement(csSource, null, colStateRef,
					modelFactory.stateExpression(csSource,
							colStateRef.expressionScope(), newStateAndID.left),
					false);
			assign.setTargetTemp(originalStmt.target());
			assign.setSourceTemp(originalStmt.source());
			result.add(Semantics.newTransition(
					universe.and(oldPC, newColState.getPathCondition()), pid,
					assign, atomicLockAction));
		}
		return result;
	}

	// TODO
	private List<Transition> enabledTransitionsOfUpdateStatement(State state,
			int pid, UpdateStatement update, AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		CIVLSource source = update.getSource();
		Expression collator = update.collator();
		CIVLFunction updateFunction = update.function();
		Expression[] arguments = update.arguments();
		int numArgs = arguments.length;
		Evaluation eval;
		NumericExpression place, gqueueLength;
		SymbolicExpression collatorHandle, collatorComp, gcollatorHandle,
				gcollatorComp, gstateQueue;
		int qLength, placeID;
		String process = state.getProcessState(pid).name();
		SymbolicExpression[] argumentValues = new SymbolicExpression[numArgs];
		SymbolicUtility symbolicUtil = evaluator.symbolicUtility();

		eval = this.evaluator.evaluate(state, pid, collator);
		collatorHandle = eval.value;
		state = eval.state;
		for (int i = 0; i < numArgs; i++) {
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		eval = this.evaluator.dereference(collator.getSource(), state, process,
				collator, collatorHandle, false);
		collatorComp = eval.value;
		state = eval.state;
		place = (NumericExpression) universe.tupleRead(collatorComp,
				universe.intObject(0));
		placeID = symbolicUtil.extractInt(source, place);
		gcollatorHandle = universe.tupleRead(collatorComp,
				universe.intObject(1));
		eval = this.evaluator.dereference(collator.getSource(), state, process,
				collator, gcollatorHandle, false);
		gcollatorComp = eval.value;
		state = eval.state;
		gqueueLength = (NumericExpression) universe.tupleRead(gcollatorComp,
				universe.intObject(2));
		gstateQueue = universe.tupleRead(gcollatorComp, universe.intObject(3));
		qLength = symbolicUtil.extractInt(collator.getSource(), gqueueLength);

		List<Pair<LHSExpression, List<Expression>>> colStateRefAssignPairs = executeFunctionAtCollateState(
				source, state, pid, process, gstateQueue, qLength, place,
				placeID, collator, updateFunction, argumentValues);

		return assignPairs2Transitions(state, pid, source,
				colStateRefAssignPairs, atomicLockAction, update);
	}

	private List<Transition> assignPairs2Transitions(State state, int pid,
			CIVLSource source,
			List<Pair<LHSExpression, List<Expression>>> colStateRefAssignPairs,
			AtomicLockAction atomicLockAction, Statement originalStmt) {
		List<Transition> result = new LinkedList<>();
		BooleanExpression pc = state.getPathCondition();
		List<List<Pair<LHSExpression, Expression>>> assignPairs = perumtations(
				colStateRefAssignPairs, colStateRefAssignPairs.size() - 1);
		Statement assign;

		for (List<Pair<LHSExpression, Expression>> assignPairList : assignPairs) {
			assign = modelFactory.parallelAssignStatement(source,
					assignPairList);
			assign.setTargetTemp(originalStmt.target());
			assign.setSourceTemp(originalStmt.source());
			result.add(
					Semantics.newTransition(pc, pid, assign, atomicLockAction));
		}
		return result;
	}

	private List<List<Pair<LHSExpression, Expression>>> perumtations(
			List<Pair<LHSExpression, List<Expression>>> colStateRefAssignPairs,
			int start) {
		List<List<Pair<LHSExpression, Expression>>> result = new ArrayList<>();
		Pair<LHSExpression, List<Expression>> myPair = colStateRefAssignPairs
				.get(start);

		if (start == 0) {
			for (Expression rhs : myPair.right) {
				List<Pair<LHSExpression, Expression>> pairList = new ArrayList<>();

				pairList.add(new Pair<>(myPair.left, rhs));
				result.add(pairList);
			}
		} else {
			List<List<Pair<LHSExpression, Expression>>> previousResult = perumtations(
					colStateRefAssignPairs, start - 1);

			for (Expression rhs : myPair.right) {
				for (List<Pair<LHSExpression, Expression>> list : previousResult) {
					List<Pair<LHSExpression, Expression>> newList = new ArrayList<>(
							list);

					newList.add(new Pair<>(myPair.left, rhs));
					result.add(newList);
				}
			}
		}
		return result;
	}

	private List<Pair<LHSExpression, List<Expression>>> executeFunctionAtCollateState(
			CIVLSource source, State state, int pid, String process,
			SymbolicExpression gstateQueue, int qLength,
			NumericExpression place, int placeID, Expression collator,
			CIVLFunction function, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		final int IDLE = 0;
		Evaluation eval;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		NumericExpression idle = universe.integer(IDLE);
		List<Pair<LHSExpression, List<Expression>>> colStateRefAssignPairs = new ArrayList<>();
		LHSExpression stateQueueExpr = modelFactory.dotExpression(source,
				modelFactory.dereferenceExpression(source,
						modelFactory.dotExpression(source, modelFactory
								.dereferenceExpression(source, collator), 1)),
				3);// collator->gcollator->queue

		for (int i = 0; i < qLength; i++) {
			NumericExpression queueIndex = universe.integer(i);
			SymbolicExpression gstateHandle = universe.arrayRead(gstateQueue,
					queueIndex), gstate;
			SymbolicExpression mystatus;
			BooleanExpression isIdleState;
			ResultType result;

			eval = this.evaluator.dereference(source, state, process, collator,
					gstateHandle, false);
			gstate = eval.value;
			state = eval.state;
			mystatus = universe.arrayRead(
					universe.tupleRead(gstate, universe.intObject(0)), place);
			isIdleState = universe.equals(mystatus, idle);
			result = reasoner.valid(isIdleState).getResultType();
			if (result == ResultType.YES) {
				int colStateID = modelFactory.getStateRef(source,
						universe.tupleRead(gstate, universe.intObject(1)));
				State colState = stateFactory.getStateByReference(colStateID);
				Collection<State> newColStates;
				LHSExpression colStateRefExpr = modelFactory.dotExpression(
						source,
						modelFactory.dereferenceExpression(source,
								modelFactory.subscriptExpression(source,
										stateQueueExpr, modelFactory
												.integerLiteralExpression(
														source,
														BigInteger
																.valueOf(i)))),
						1);// (*queue[i]).state

				colState = stateFactory.addExternalProcess(colState, state, pid,
						placeID, function, argumentValues);
				newColStates = collateExecutor.run2Completion(state, pid,
						colState, this.civlConfig);

				Pair<LHSExpression, List<Expression>> myColStateUpdatePair = this
						.getCollateStateUpdateExpressions(pid, colStateRefExpr,
								newColStates);

				colStateRefAssignPairs.add(myColStateUpdatePair);
			}
		}
		return colStateRefAssignPairs;
	}

	private Pair<LHSExpression, List<Expression>> getCollateStateUpdateExpressions(
			int pid, LHSExpression colStateRef, Collection<State> colStates) {
		List<Expression> stateExpressions = new ArrayList<>();
		CIVLSource csSource = colStateRef.getSource();

		for (State colState : colStates) {
			stateExpressions.add(modelFactory.stateExpression(csSource,
					colStateRef.expressionScope(),
					stateFactory.saveState(colState, pid).left));
		}
		return new Pair<>(colStateRef, stateExpressions);
	}

	/* ************************ Package-private Methods ******************** */
	/**
	 * Computes the set of enabled transitions of a system function call.
	 * 
	 * @param source
	 *            the source of the call statement
	 * @param state
	 *            the current state
	 * @param call
	 *            the system call statement
	 * @param pathCondition
	 *            the current path condition
	 * @param pid
	 *            the PID
	 * @param atomicLockAction
	 *            the atomic lock action
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<Transition> getEnabledTransitionsOfSystemCall(
			CIVLSource source, State state, CallOrSpawnStatement call,
			BooleanExpression pathCondition, int pid,
			AtomicLockAction atomicLockAction)
			throws UnsatisfiablePathConditionException {
		SystemFunction sysFunction = (SystemFunction) call.function();
		String libraryName = sysFunction.getLibrary();

		if (sysFunction.needsEnabler()) {
			try {
				LibraryEnabler libEnabler = libraryEnabler(source, libraryName);

				return libEnabler.enabledTransitions(state, call, pathCondition,
						pid, atomicLockAction);
			} catch (LibraryLoaderException exception) {
				return Arrays.asList(Semantics.newTransition(pathCondition, pid,
						call, atomicLockAction));
			}
		} else {
			return Arrays.asList(Semantics.newTransition(pathCondition, pid,
					call, atomicLockAction));
		}
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
	 * @param the
	 *            ID of the statement in its source location
	 * @param newGuardMap
	 *            a map from process ID to map of statement and the value of its
	 *            guard at the current state
	 * @return The new path condition. False if the guard is not satisfiable
	 *         under the path condition.
	 */
	private BooleanExpression newPathCondition(State state, int pid,
			Statement statement, int statementId,
			BooleanExpression newGuardMap[][]) {
		BooleanExpression guard;
		BooleanExpression myMap[] = newGuardMap != null
				? newGuardMap[pid]
				: null;

		guard = myMap != null ? myMap[statementId] : null;
		if (guard == null)
			guard = getGuard(statement, pid, state);
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
		return (BooleanExpression) universe
				.canonic(universe.and(pathCondition, guard));
	}
}
