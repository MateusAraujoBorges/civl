package edu.udel.cis.vsl.civl.semantics.common;

import java.util.LinkedList;
import java.util.NoSuchElementException;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.seq.TransitionIterator;
import edu.udel.cis.vsl.gmc.seq.TransitionSetIF;

/**
 * This class defines the regular transition iterator of {@link TransitionSetIF}
 * , the iterator will iterate the {@link TransitionSetIF} in a fix order.
 * 
 * @author Yihao Yan (yihaoyan)
 *
 */
public class CommonTransitionIterator extends TransitionIterator<State, Transition> {
	/**
	 * The source transition set.
	 */
	private TransitionSet transitionSet;
	/**
	 * A list of indexes of the transition set.
	 */
	private LinkedList<Integer> indexes;

	/**
	 * The number of transitions that have been consumed.
	 */
	private int numConsumed = 0;

	/**
	 * <ul>
	 * <li>offSet = 0 when this iterator iterates an ample set;</li>
	 * <li>offSet = sizeof(ampleSet) when this iterator iterates an ample set
	 * complement;</li>
	 * </ul>
	 */
	private int offSet = 0;

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
		if (indexes.size() == 0)
			throw new NoSuchElementException();

		return transitionSet.get(indexes.peek());
	}

	@Override
	public boolean hasNext() {
		return indexes.size() > 0;
	}

	@Override
	public Transition next() {
		if (indexes.size() == 0)
			throw new NoSuchElementException();

		numConsumed++;
		return transitionSet.get(indexes.pop());
	}

	@Override
	public int numConsumed() {
		return numConsumed + offSet;
	}

	public void setOffSet(int offSet) {
		this.offSet = offSet;
	}

}
