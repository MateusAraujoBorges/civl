package edu.udel.cis.vsl.civl.kripke.common;

import java.util.Collection;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.StateManager;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.gmc.TraceStepIF;

public class ColStateManager extends CommonStateManager
		implements StateManager {

	private Set<State> finalColState;

	public ColStateManager(Enabler enabler, Executor executor,
			SymbolicAnalyzer symbolicAnalyzer, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		super(enabler, executor, symbolicAnalyzer, errorLogger, config);
	}

	// @Override
	// public TraceStepIF<Transition, State> nextStateWork(State state,
	// Transition transition) throws UnsatisfiablePathConditionException {
	// int pid = transition.pid();
	// Transition firstTransition = transition;
	// State oldState = state;
	// StateStatus stateStatus;
	// TraceStep traceStep = new CommonTraceStep(pid);
	// String process;
	//
	// pid = transition.pid();
	// process = "p" + pid;
	// state = executor.execute(state, pid, transition);
	// traceStep.addAtomicStep(new CommonAtomicStep(state, transition));
	// return null;
	// }

	@Override
	public TraceStepIF<Transition, State> nextState(State state,
			Transition transition) {
		TraceStepIF<Transition, State> result;

		try {
			result = nextStateWork(state, transition);
		} catch (UnsatisfiablePathConditionException e) {
			// problem is the interface requires an actual State
			// be returned. There is no concept of executing a
			// transition and getting null or an exception.
			// since the error has been logged, just return
			// some state with false path condition, so there
			// will be no next state...
			result = new NullTraceStep(state.setPathCondition(falseExpr));
		}

		State resultState = result.getFinalState();

		if (isFinalCollateState(resultState))
			this.finalColState.add(resultState);
		return result;
	}

	private boolean isFinalCollateState(State state) {
		int numProcs = state.numProcs();

		for (int i = 0; i < numProcs; i++) {
			ProcessState proc = state.getProcessState(i);

			if (proc != null && !proc.getLocation().isSleep())
				return false;
		}
		return true;
	}

	public Collection<State> getFinalCollateStates() {
		return this.finalColState;
	}

}
