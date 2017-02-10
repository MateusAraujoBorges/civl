package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.AtomicLockAction;
import edu.udel.cis.vsl.civl.semantics.common.CommonEvaluator;
import edu.udel.cis.vsl.civl.semantics.common.CommonExecutor;
import edu.udel.cis.vsl.civl.semantics.common.CommonLibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.common.CommonLibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.common.CommonMemoryUnitEvaluator;
import edu.udel.cis.vsl.civl.semantics.common.CommonNoopTransition;
import edu.udel.cis.vsl.civl.semantics.common.CommonSymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.common.CommonTransition;
import edu.udel.cis.vsl.civl.semantics.common.CommonTransitionSet;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * Entry point of the module civl.semantics.
 * 
 * @author zmanchun
 * 
 */
public class Semantics {

	/**
	 * Creates a new instance of library executor loader.
	 * 
	 * @return The new library executor loader.
	 */
	public static LibraryExecutorLoader newLibraryExecutorLoader(LibraryEvaluatorLoader libEvaluatorLoader,
			CIVLConfiguration civlConfig) {
		return new CommonLibraryExecutorLoader(libEvaluatorLoader, civlConfig);
	}

	/**
	 * Creates a new instance of library evaluator loader.
	 * 
	 * @return The new library evaluator loader.
	 */
	public static LibraryEvaluatorLoader newLibraryEvaluatorLoader(CIVLConfiguration civlConfig) {
		return new CommonLibraryEvaluatorLoader(civlConfig);
	}

	/**
	 * Creates a new instance of CIVL executor.
	 * 
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param stateFactory
	 *            The state factory of the system.
	 * @param log
	 *            The error logger of the system.
	 * @param loader
	 *            The library executor loader for executing system functions.
	 * @param evaluator
	 *            The CIVL evaluator for evaluating expressions.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param errLogger
	 *            The error logger for reporting execution errors.
	 * @param civlConfig
	 *            The CIVL configuration.
	 * @return The new CIVL executor.
	 */
	public static Executor newExecutor(ModelFactory modelFactory, StateFactory stateFactory,
			LibraryExecutorLoader loader, Evaluator evaluator, SymbolicAnalyzer symbolicAnalyzer,
			CIVLErrorLogger errLogger, CIVLConfiguration civlConfig) {
		return new CommonExecutor(modelFactory, stateFactory, loader, evaluator, symbolicAnalyzer, errLogger,
				civlConfig);
	}

	/**
	 * Creates a new instance of CIVL evaluator.
	 * 
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param stateFactory
	 *            The state factory of the system.
	 * @param loader
	 *            The library evaluator loader for evaluating the guards of
	 *            system functions.
	 * @param symbolicUtil
	 *            The symbolic utility for manipulations of symbolic
	 *            expressions.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param errLogger
	 *            The error logger for reporting execution errors.
	 * @return The new CIVL evaluator.
	 */
	public static Evaluator newEvaluator(ModelFactory modelFactory, StateFactory stateFactory,
			LibraryEvaluatorLoader loader, LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, MemoryUnitFactory memUnitFactory, CIVLErrorLogger errLogger,
			CIVLConfiguration config) {
		return new CommonEvaluator(modelFactory, stateFactory, loader, loaderExec, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, errLogger, config);
	}

	/**
	 * Creates a new instance of symbolic analyzer.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 * @param modelFactory
	 *            The model factory to be used.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @return The new symbolic analyzer.
	 */
	public static SymbolicAnalyzer newSymbolicAnalyzer(CIVLConfiguration civlConfig, SymbolicUniverse universe,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil) {
		return new CommonSymbolicAnalyzer(civlConfig, universe, modelFactory, symbolicUtil);
	}

	/**
	 * Create a new CIVL transition.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing the
	 *            statement of the transition
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param statement
	 *            The statement corresponding to this transition, which should
	 *            be atomic and deterministic.
	 * @return A new transition with the given path condition and statement.
	 */
	public static Transition newTransition(BooleanExpression pathCondition, int pid, Statement statement,
			AtomicLockAction atomicLockAction) {
		return new CommonTransition(pathCondition, pid, statement, atomicLockAction);
	}

	/**
	 * 
	 * @param pathCondition
	 * @param pid
	 * @param statement
	 * @param simplifyState
	 * @param atomicLockAction
	 * @return
	 */
	public static Transition newTransition(BooleanExpression pathCondition, int pid, Statement statement,
			boolean simplifyState, AtomicLockAction atomicLockAction) {
		return new CommonTransition(pathCondition, pid, statement, simplifyState, atomicLockAction);
	}

	/**
	 * Create a new Noop transition.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing the
	 *            statement of the transition
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param target
	 *            The target location of the process after this transition
	 * @return A new transition with the given path condition and target
	 *         location.
	 */
	public static NoopTransition newNoopTransition(BooleanExpression pathCondition, int pid,
			BooleanExpression assumption, Statement statement, boolean symplifyState,
			AtomicLockAction atomicLockAction) {
		return new CommonNoopTransition(pathCondition, pid, assumption, statement, symplifyState, atomicLockAction);
	}

	/**
	 * Create a new transition set.
	 * 
	 * @param state
	 *            The target state.
	 * @param containingAllEnabled
	 *            does this contain all enabled transitions
	 * @return A new transition set.
	 */
	public static TransitionSet newTransitionSet(State state, boolean containingAllEnabled) {
		return new CommonTransitionSet(state, containingAllEnabled);
	}

	/**
	 * Create a new transition set initialized with a set of transitions.
	 * 
	 * @param state
	 *            The target state.
	 * @param transitions
	 *            The list of transitions used to initialize the transition set.
	 * @param containingAllEnabled
	 *            does this contain all enabled transitions
	 * @return A new transition set.
	 */
	public static TransitionSet newTransitionSet(State state, List<Transition> transitions,
			boolean containingAllEnabled) {
		return new CommonTransitionSet(state, transitions, containingAllEnabled);
	}

	public static MemoryUnitExpressionEvaluator newMemoryUnitEvaluator(Evaluator evaluator,
			MemoryUnitFactory memUnitFactory) {
		return new CommonMemoryUnitEvaluator(evaluator.symbolicUtility(), evaluator, memUnitFactory,
				evaluator.universe());
	}
}
