package edu.udel.cis.vsl.civl.kripke.common;

import java.util.Collection;
import java.util.HashSet;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.predicate.IF.CIVLStatePredicate;
import edu.udel.cis.vsl.civl.predicate.IF.Predicates;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.seq.DfsSearcher;

public class CollateExecutor {
	private Enabler enabler;
	private Executor executor;
	private CIVLErrorLogger errorLogger;
	private CIVLConfiguration config;
	private CIVLStatePredicate predicate = Predicates.newTrivialPredicate();

	public CollateExecutor(Enabler enabler, Executor executor,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		this.enabler = enabler;
		this.executor = executor;
		this.errorLogger = errorLogger;
		this.config = new CIVLConfiguration(config);
		this.config.setCollectHeaps(true);
		this.config.setCollectScopes(true);
		this.config.setCollectProcesses(true);
		this.config.setCheckMemoryLeak(false);
		this.config.setCheckExpressionError(false);
		// this.config.setSimplify(false);
		this.config.setInSubprogram(true);
	}

	// public CollateExecutor(Evaluator mainEvaluator, CIVLErrorLogger
	// errorLogger,
	// CIVLConfiguration config) {
	// this.config = new CIVLConfiguration(config);
	// this.config.setCollectHeaps(true);
	// this.config.setCollectScopes(true);
	// this.config.setCollectProcesses(true);
	// this.config.setCheckMemoryLeak(false);
	// this.config.setCheckExpressionError(false);
	//
	// LibraryEvaluatorLoader libraryEvaluatorLoader = Semantics
	// .newLibraryEvaluatorLoader(this.config);
	// LibraryExecutorLoader libraryExecutorLoader = Semantics
	// .newLibraryExecutorLoader(libraryEvaluatorLoader, this.config);
	// MemoryUnitFactory memoryUnitFactory = States
	// .newImmutableMemoryUnitFactory(mainEvaluator.universe(),
	// mainEvaluator.modelFactory());
	// Evaluator evaluator = Semantics.newEvaluator(
	// mainEvaluator.modelFactory(), mainEvaluator.stateFactory(),
	// libraryEvaluatorLoader,
	// Semantics.newLibraryExecutorLoader(libraryEvaluatorLoader,
	// this.config),
	// mainEvaluator.symbolicUtility(),
	// mainEvaluator.symbolicAnalyzer(), memoryUnitFactory,
	// errorLogger, this.config);
	//
	// this.executor = Semantics.newExecutor(mainEvaluator.modelFactory(),
	// mainEvaluator.stateFactory(), libraryExecutorLoader, evaluator,
	// mainEvaluator.symbolicAnalyzer(), errorLogger, this.config);
	// this.enabler = Kripkes.newEnabler(mainEvaluator.stateFactory(),
	// evaluator, this.executor, mainEvaluator.symbolicAnalyzer(),
	// memoryUnitFactory,
	// Kripkes.newLibraryEnablerLoader(libraryEvaluatorLoader,
	// this.config),
	// errorLogger, this.config);
	// this.errorLogger = errorLogger;
	// }

	Collection<State> run2Completion(State realState, int pid, State initState,
			CIVLConfiguration oldConfig) {
		ColStateManager colStateManager = new ColStateManager(enabler, executor,
				executor.evaluator().symbolicAnalyzer(), errorLogger, config);
		DfsSearcher<State, Transition> searcher = new DfsSearcher<State, Transition>(
				enabler, colStateManager, predicate, config.saveStates());

		executor.stateFactory().setConfiguration(this.config);
		executor.evaluator().setConfiguration(this.config);
		executor.setConfiguration(this.config);
		try {
			initState = executor.stateFactory().canonic(initState, false, false,
					false, new HashSet<>(0));
		} catch (CIVLHeapException e) {
			// ignore
		}
		if (this.config.showTransitions() || this.config.showStates()
				|| config.showSavedStates() || config.debugOrVerbose())
			config.out().println("********************************\n"
					+ "Process " + realState.getProcessState(pid).name()
					+ " at State " + realState.getCanonicId()
					+ ": start executing sub-program on collate states.");
		if (this.config.showStates() || config.showSavedStates()
				|| config.debugOrVerbose()) {
			config.out().println(executor.evaluator().symbolicAnalyzer()
					.stateToString(initState));
		}
		while (searcher.search(initState));
		if (this.config.showTransitions() || this.config.showStates()
				|| config.showSavedStates() || config.debugOrVerbose())
			config.out().println(
					"Finish executing sub-program on collate states.\n********************************");
		executor.evaluator().setConfiguration(oldConfig);
		executor.stateFactory().setConfiguration(oldConfig);
		executor.setConfiguration(oldConfig);
		return colStateManager.getFinalCollateStates();
	}
}
