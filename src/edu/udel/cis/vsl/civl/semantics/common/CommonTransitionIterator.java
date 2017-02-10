package edu.udel.cis.vsl.civl.semantics.common;

import java.util.LinkedList;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionIterator;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.TransitionSetIF;

/**
 * This class defines the regular transition iterator of {@link TransitionSetIF}
 * , the iterator will iterate the {@link TransitionSetIF} in an order manner.
 * 
 * @author yanyihao
 *
 */
public class CommonTransitionIterator implements TransitionIterator {
	/**
	 * The source transition set.
	 */
	private TransitionSet transitionSet;
	/**
	 * A list of indexes of the transition set.
	 */
	private LinkedList<Integer> indexes;

	public CommonTransitionIterator(TransitionSet transitionSet) {
		this.transitionSet = transitionSet;
		indexes = new LinkedList<>();

		int size = transitionSet.size();

		for (int i = 0; i < size; i++) {
			indexes.add(i);
		}
	}

	@Override
	public TransitionSetIF<State, Transition> getTransitionSet() {
		return transitionSet;
	}

	@Override
	public Transition peek() {
		return transitionSet.get(indexes.peek());
	}

	@Override
	public boolean hasNext() {
		return indexes.size() > 0;
	}

	@Override
	public Transition next() {
		transitionSet.incrementNumExecuted();
		return transitionSet.get(indexes.pop());
	}

}
