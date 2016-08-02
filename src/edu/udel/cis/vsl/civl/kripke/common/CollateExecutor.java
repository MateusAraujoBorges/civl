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
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.DfsSearcher;

public class CollateExecutor {
	private Enabler enabler;
	private Executor executor;
	private CIVLErrorLogger errorLogger;
	private CIVLConfiguration config;
	private CIVLStatePredicate predicate = Predicates.newTrivialPredicate();

	public CollateExecutor(Enabler enabler, Executor executor, CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		this.enabler = enabler;
		this.executor = executor;
		this.errorLogger = errorLogger;
		this.config = new CIVLConfiguration(config);
		this.config.setCollectHeaps(true);
		this.config.setCollectScopes(true);
		this.config.setCollectProcesses(true);
		this.config.setCheckMemoryLeak(false);
	}

	Collection<State> run2Completion(State initState) {
		ColStateManager colStateManager = new ColStateManager(enabler, executor,
				executor.evaluator().symbolicAnalyzer(), errorLogger, config);
		DfsSearcher<State, Transition, TransitionSequence> searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, colStateManager, predicate);

		try {
			initState = executor.stateFactory().canonic(initState, false, false, false, new HashSet<>(0));
		} catch (CIVLHeapException e) {
			// ignore
		}
		if (this.config.showTransitions() || this.config.showStates() || config.showSavedStates()
				|| config.debugOrVerbose())
			config.out().println("********************************\nStart executing sub-program on collate states.");
		if (this.config.showStates() || config.showSavedStates() || config.debugOrVerbose())
			config.out().println(executor.evaluator().symbolicAnalyzer().stateToString(initState));
		while (searcher.search(initState))
			;
		if (this.config.showTransitions() || this.config.showStates() || config.showSavedStates()
				|| config.debugOrVerbose())
			config.out().println("Finish executing sub-program on collate states.\n********************************");

		return colStateManager.getFinalCollateStates();
	}
}
