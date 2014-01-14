/**
 * 
 */
package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.Executor.StateStatusKind;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.transition.ChooseTransition;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.gmc.StateManagerIF;

/**
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class StateManager implements StateManagerIF<State, Transition> {

	/***************************** Instance Fields ***************************/

	/**
	 * The unique executor instance used by the system
	 */
	private Executor executor;

	/**
	 * The flag to turn on/off printing of debugging information.
	 */
	private boolean debug = false;

	/**
	 * The maximal number of processes at a state, initialized as 0.
	 */
	private int maxProcs = 0;

	/**
	 * The output stream to be used in this class to print states, transitions,
	 * warnings, etc.
	 */
	private PrintStream out = null;

	/**
	 * Save states during search?
	 */
	private boolean saveStates = true;

	/**
	 * Print saved states (i.e., canonicalized states)?
	 */
	private boolean showSavedStates = false;

	/**
	 * Print all states (including states that are not saved)?
	 */
	private boolean showStates = false;

	/**
	 * Print transitions?
	 */
	private boolean showTransitions = false;

	/**
	 * Simplify state returned by nextState?
	 */
	private boolean simplify = true;

	/**
	 * The unique state factory used by the system.
	 */
	private StateFactory stateFactory;

	/**
	 * Turn on/off verbose mode.
	 */
	private boolean verbose = false;

	/******************************* Constructor *****************************/

	/**
	 * 
	 * @param executor
	 *            The unique executor to by used in the system.
	 */
	public StateManager(Executor executor) {
		this.executor = executor;
		this.stateFactory = executor.stateFactory();
	}

	/***************************** Private Methods ***************************/

	/**
	 * Execute an deterministic atomic block ($atom), supporting nested atom
	 * blocks, require that the whole block is finite, non-blocking and
	 * deterministic. Otherwise, a warning or an error will be reported.
	 * 
	 * Precondition:
	 * <code> location.enterAtom() == true && location == state.getProcessState(pid).getLocation()</code>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The id of the process being executing
	 * @param location
	 *            The start location of the atomic block
	 * @param print
	 *            True iff each step is to be printed.
	 * @return The resulting state after executing the $atom block
	 */
	private State executeAtomBlock(State state, int pid, Location location,
			boolean print) {
		ProcessState p;
		CIVLSource atomicStart = location.getSource();
		Location newLocation = location;
		State newState = state;
		int stateCounter = 0;
		Statement start = location.getOutgoing(0);
		Pair<StateStatusKind, State> init;

		assert location.enterAtom() == true
				&& location.id() == state.getProcessState(pid).getLocation()
						.id() && location.getNumOutgoing() == 1;
		init = executor.executeStatement(state, location, start, pid);
		if (init.left == StateStatusKind.BLOCKED) {
			executor.evaluator().reportError(
					new CIVLStateException(ErrorKind.OTHER, Certainty.CONCRETE,
							"Execution blocked in $atom", newState, newLocation
									.getSource()));
		} else {
			newState = init.right;
			newLocation = newState.getProcessState(pid).getLocation();
			if (print) {
				printStatement(start, AtomicKind.ATOM_ENTER,
						newState.getProcessState(pid));
			}
		}
		while (true) {
			boolean statementExecuted = false;
			State currentState = newState;
			Statement executedStatement = null;

			switch (newLocation.atomicKind()) {
			case ATOM_ENTER:
				newState = executeAtomBlock(newState, pid, newLocation, print);
				stateCounter++;
				statementExecuted = true;
				break;
			case ATOM_EXIT:
				assert (newLocation.getNumOutgoing() == 1);
				newState = executor.executeStatement(newState, newLocation,
						newLocation.getOutgoing(0), pid).right;
				executedStatement = newLocation.getOutgoing(0);
				if (print) {
					printStatement(executedStatement, AtomicKind.ATOM_EXIT,
							newState.getProcessState(pid));
				}
				assert newState != null;
				return newState;
			default:
				for (Statement s : newLocation.outgoing()) {
					Pair<StateStatusKind, State> temp = executor
							.executeStatement(newState, newLocation, s, pid);

					switch (temp.left) {
					case NONDETERMINISTIC:
						executor.evaluator()
								.reportError(
										new CIVLStateException(
												ErrorKind.OTHER,
												Certainty.CONCRETE,
												"Non-determinism is found in $atom block.",
												newState, newLocation
														.getSource()));
						// throw new UnsatisfiablePathConditionException();
					case NORMAL:
						if (statementExecuted) {
							executor.evaluator()
									.reportError(
											new CIVLStateException(
													ErrorKind.OTHER,
													Certainty.CONCRETE,
													"Non-determinism is found in $atom block.",
													newState, newLocation
															.getSource()));
							// throw new UnsatisfiablePathConditionException();
						}
						statementExecuted = true;
						newState = temp.right;
						executedStatement = s;
						break;
					default:// current statement is blocked, continue to try
							// executing another statement from the same
							// location
						continue;
					}
				}
			}
			// current location is blocked
			if (!statementExecuted) {
				executor.evaluator()
						.reportError(
								new CIVLStateException(
										ErrorKind.OTHER,
										Certainty.CONCRETE,
										"Undesired blocked location is detected in $atom block.",
										currentState, newLocation.getSource()));
				// throw new UnsatisfiablePathConditionException();
			}
			// warning for possible infinite atomic block
			if (stateCounter != 0 && stateCounter % 1024 == 0) {
				out.println("Warning: " + (stateCounter)
						+ " states in $atom block at "
						+ atomicStart.getLocation() + ".");
			}
			stateCounter++;
			p = newState.getProcessState(pid);
			if (print && executedStatement != null) {
				printStatement(executedStatement, newLocation.atomicKind(), p);
			}
			if (p != null && !p.hasEmptyStack())
				newLocation = p.getLocation();
			else {
				throw new CIVLInternalException("Unreachable",
						newLocation.getSource());
			}
		}
	}

	/**
	 * Execute a sequence of purely local statements or statements defined in an
	 * $atomic block of a certain process
	 * 
	 * @param state
	 *            The state to start with
	 * @param pid
	 *            id of the executing process
	 * @param location
	 *            The start location of the execution
	 * @param atomic
	 *            True iff executing statements in an atomic block; false iff
	 *            executing statements found to be purely local
	 * @return The resulting state
	 */
	private State executeAtomicOrPurelyLocalStatements(State state, int pid,
			Location location, boolean atomic, boolean print) {
		Location pLocation = location;
		ProcessState p = state.getProcessState(pid);
		State newState = state;
		Statement executedStatement = null;

		assert atomic || pLocation.isPurelyLocal();
		while ((!atomic && pLocation != null && pLocation.isPurelyLocal())
				|| (atomic && pLocation != null)) {
			if (pLocation.isLoopPossible()) {
				return newState;
			}
			executedStatement = null;
			switch (pLocation.atomicKind()) {
			case NONE:
				boolean executed = false;
				State oldState = newState;

				for (Statement s : pLocation.outgoing()) {
					Pair<StateStatusKind, State> temp = executor
							.executeStatement(oldState, pLocation, s, pid);

					switch (temp.left) {
					case NONDETERMINISTIC:
						// finds non-determinism, go back to previous state
						return oldState;
					case NORMAL:
						if (executed) {
							// finds non-determinism, go back to previous
							// state
							return oldState;
						}
						executed = true;
						newState = temp.right;
						executedStatement = s;
						break;
					default:// BLOCKED, continue to try executing next
							// statement
						continue;
					}
				}
				if (!executed) {// blocked
					oldState = stateFactory.releaseAtomicLock(oldState);
					return oldState;
				}
				break;
			case ATOM_ENTER:
				newState = executeAtomBlock(newState, pid, pLocation, print);
				break;
			case ATOMIC_ENTER:
				if (atomic) {
					assert !stateFactory.lockedByAtomic(newState)
							|| stateFactory.processInAtomic(newState).getPid() == pid;
					newState = executor.executeStatement(newState, pLocation,
							pLocation.getOutgoing(0), pid).right;
					p = newState.getProcessState(pid).incrementAtomicCount();
					newState = stateFactory.setProcessState(newState, p, pid);
					newState = stateFactory.getAtomicLock(newState, pid);
					executedStatement = pLocation.getOutgoing(0);
				} else {
					newState = executeAtomicOrPurelyLocalStatements(newState,
							pid, pLocation, true, print);
				}
				break;
			case ATOMIC_EXIT:
				if (!atomic)
					throw new CIVLInternalException("Unreachable",
							pLocation.getSource());
				assert stateFactory.processInAtomic(newState).getPid() == pid;
				newState = executor.executeStatement(newState, pLocation,
						pLocation.getOutgoing(0), pid).right;
				p = newState.getProcessState(pid).decrementAtomicCount();
				executedStatement = pLocation.getOutgoing(0);
				newState = stateFactory.setProcessState(newState, p, pid);
				if (!p.inAtomic()) {
					newState = stateFactory.releaseAtomicLock(newState);
					if (print) {
						printStatement(executedStatement,
								AtomicKind.ATOMIC_EXIT, p);
					}
					return newState;
				}
				break;
			default:
				throw new CIVLInternalException("Unreachable",
						pLocation.getSource());
			}
			p = newState.getProcessState(pid);
			if (print && executedStatement != null) {
				printStatement(executedStatement, pLocation.atomicKind(), p);
			}
			if (p != null && !p.hasEmptyStack())
				pLocation = p.peekStack().location();
			else
				pLocation = null;
		}
		return newState;
	}

	private State nextStateWork(State state, Transition transition)
			throws UnsatisfiablePathConditionException {
		int pid;
		Statement statement;
		int numProcs;
		ProcessState p;
		Location currentLocation;
		boolean printTransitions = verbose || debug || showTransitions;

		assert transition instanceof SimpleTransition;
		pid = ((SimpleTransition) transition).pid();
		p = state.getProcessState(pid);
		currentLocation = p.getLocation();
		switch (currentLocation.atomicKind()) {
		case ATOMIC_ENTER:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomicOrPurelyLocalStatements(state, pid,
					currentLocation, true, printTransitions);
			break;
		case ATOMIC_EXIT:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomicOrPurelyLocalStatements(state, pid,
					currentLocation, true, printTransitions);
			break;
		case ATOM_ENTER:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomBlock(state, pid, currentLocation,
					printTransitions);
			break;
		case ATOM_EXIT:
			throw new CIVLInternalException("Unreachable",
					currentLocation.getSource());
		default:// execute a normal transition
			if (printTransitions) {
				out.println();
				out.print(state + ", ");
				printTransitionLong(out, transition);
				out.println(";");
			}
			state = state.setPathCondition(((SimpleTransition) transition)
					.pathCondition());
			statement = ((SimpleTransition) transition).statement();
			if (transition instanceof ChooseTransition) {
				if (statement instanceof StatementList) {
					state = executor.executeStatementList(state, pid,
							(StatementList) statement,
							((ChooseTransition) transition).value());
				} else {
					assert statement instanceof ChooseStatement;
					state = executor.executeChoose(state, pid,
							(ChooseStatement) statement,
							((ChooseTransition) transition).value());
				}
			} else {
				state = executor.execute(state, pid, statement);
			}
			// sometimes the execution might allow the process to grab the
			// atomic lock
			if (executor.stateFactory().lockedByAtomic(state)) {
				currentLocation = state.getProcessState(pid).getLocation();
				state = executeAtomicOrPurelyLocalStatements(state, pid,
						currentLocation, true, printTransitions);
			}
		}
		// do nothing when process pid terminates and is removed from the state
		if (!stateFactory.lockedByAtomic(state) && state.numProcs() > pid) {
			p = state.getProcessState(pid);
			if (p != null && !p.hasEmptyStack()) {
				Location newLocation = p.peekStack().location();

				// execute purely local statements of the current process
				// greedily
				if (newLocation != null && newLocation.isPurelyLocal()) {
					state = executeAtomicOrPurelyLocalStatements(state, pid,
							newLocation, false, printTransitions);
				}
			}
		}
		if (printTransitions) {
			out.print("--> ");
		}

		state = stateFactory.collectScopes(state);
		// TODO: try this simplification out, see how it works:
		if (simplify) {
			state = stateFactory.simplify(state);
		}
		if (saveStates) {
			state = stateFactory.canonic(state);
		} else {
			state.commit();
		}
		if (verbose || debug || showTransitions) {
			out.println(state);
		}
		if (debug || verbose || showStates || showSavedStates) {
			out.println();
			state.print(out);
		}
		numProcs = state.numProcs();
		if (numProcs > maxProcs)
			maxProcs = numProcs;
		return state;
	}

	private void printStatement(Statement s, AtomicKind atomicKind,
			ProcessState p) {
		CIVLSource statementSource = s.getSource();

		if (statementSource == null)
			statementSource = s.source().getSource();
		out.print("  " + s.source().id() + "->");
		if (s.target() != null)
			out.print(s.target().id() + ": ");
		else
			out.print("RET: ");
		switch (atomicKind) {
		case ATOMIC_ENTER:
			out.print(s.toString() + " ");
			out.print(p.atomicCount() - 1);
			break;
		case ATOMIC_EXIT:
			out.print(s.toString() + " ");
			out.print(p.atomicCount());
			break;
		default:
			out.print(s.toString());
		}
		if (statementSource != null)
			out.println(" at " + statementSource.getSummary() + ";");
	}

	private void printTransitionPrefix(boolean printTransitions, State state,
			int pid) {
		if (printTransitions) {
			out.println();
			out.print(state + ", proc ");
			out.println(pid + ":");
		}
	}

	/*********************** Methods from StateManagerIF *********************/

	@Override
	public int getDepth(State state) {
		return state.getDepth();
	}

	@Override
	public State nextState(State state, Transition transition) {
		try {
			return nextStateWork(state, transition);
		} catch (UnsatisfiablePathConditionException e) {
			// problem is the interface requires an actual State
			// be returned. There is no concept of executing a
			// transition and getting null or an exception.
			// since the error has been logged, just stutter:
			return state;
		}

	}

	@Override
	public boolean onStack(State state) {
		return state.onStack();
	}

	@Override
	public void printAllStatesLong(PrintStream arg0) {

	}

	@Override
	public void printAllStatesShort(PrintStream arg0) {

	}

	@Override
	public void printStateLong(PrintStream out, State state) {
		state.print(out);
	}

	@Override
	public void printStateShort(PrintStream out, State state) {
		out.print(state.toString());
	}

	@Override
	public void printTransitionLong(PrintStream out, Transition transition) {
		out.print(transition.toString());
	}

	@Override
	public void printTransitionShort(PrintStream out, Transition transition) {
		out.print(transition.toString());
	}

	@Override
	public boolean seen(State state) {
		return state.seen();
	}

	@Override
	public void setDepth(State state, int value) {
		state.setDepth(value);
	}

	@Override
	public void setOnStack(State state, boolean value) {
		state.setOnStack(value);
	}

	@Override
	public void setSeen(State state, boolean value) {
		state.setSeen(value);
	}

	/************************** Other Public Methods *************************/

	public boolean getDebug() {
		return debug;
	}

	/**
	 * Returns the number of objects of type State that have been instantiated
	 * since this JVM started.
	 * 
	 * @return the number of states instantiated
	 */
	public long getNumStateInstances() {
		return stateFactory.getNumStateInstances();
	}

	/**
	 * Returns the number of states saved, i.e., made canonic.
	 * 
	 * @return the number of canonic states
	 */
	public int getNumStatesSaved() {
		return stateFactory.getNumStatesSaved();
	}

	public PrintStream getOutputStream() {
		return out;
	}

	public boolean getSaveStates() {
		return saveStates;
	}

	public boolean getShowSavedStates() {
		return showSavedStates;
	}

	public boolean getShowStates() {
		return showStates;
	}

	public boolean getShowTransitions() {
		return showTransitions;
	}

	public boolean getSimplify() {
		return simplify;
	}

	public boolean getVerbose() {
		return verbose;
	}

	/**
	 * @return The maximum number of processes in any state encountered by this
	 *         state manager.
	 */
	public int maxProcs() {
		return maxProcs;
	}

	public void setDebug(boolean value) {
		this.debug = value;
	}

	public void setSaveStates(boolean value) {
		this.saveStates = value;
	}

	public void setShowSavedStates(boolean value) {
		this.showSavedStates = value;
	}

	public void setShowStates(boolean value) {
		this.showStates = value;
	}

	public void setShowTransitions(boolean value) {
		this.showTransitions = value;
	}

	public void setSimplify(boolean value) {
		simplify = value;
	}

	public void setOutputStream(PrintStream out) {
		this.out = out;
	}

	public void setVerbose(boolean value) {
		this.verbose = value;
	}

}
