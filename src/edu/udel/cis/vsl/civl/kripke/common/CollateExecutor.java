package edu.udel.cis.vsl.civl.kripke.common;

import java.util.Collection;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.predicate.IF.Predicates;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.DfsSearcher;

public class CollateExecutor {
	private DfsSearcher<State, Transition, TransitionSequence> searcher;
	private ColStateManager colStateManager;

	public CollateExecutor(Enabler enabler, Executor executor,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		colStateManager = new ColStateManager(enabler, executor,
				executor.evaluator().symbolicAnalyzer(), errorLogger, config);
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, colStateManager, Predicates.newTrivialPredicate());
	}

	Collection<State> run2Completion(State initState) {
		while (searcher.search(initState))
			;
		return colStateManager.getFinalCollateStates();
	}
}
