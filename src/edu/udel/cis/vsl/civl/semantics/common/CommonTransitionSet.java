package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.TransitionIterator;

/**
 * A transition set contains a list of transitions and the state from which they
 * emanate.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * @author Yihao Yan (yanyihao)
 */
public class CommonTransitionSet implements TransitionSet {

	/* *************************** Instance Fields ************************* */

	/**
	 * All the transitions emanating from a certain state.
	 */
	private List<Transition> transitions;

	/**
	 * This is the state from which all the transitions in the set emanate.
	 */
	private State state;

	/**
	 * true iff the transition set contains the full enabled set.
	 */
	private boolean containingAllEnabled = false;

	/**
	 * <ul>
	 * <li>offSet = 0 when this transition set is ample set;</li>
	 * <li>offSet = sizeof(ampleset) when this transition set is ample set
	 * complement;</li>
	 * </ul>
	 */
	private int offSet = 0;

	/* ***************************** Constructors ************************** */

	/**
	 * Create an empty transition set.
	 * 
	 * @param state
	 *            The state that all transitions of this set emanate from.
	 * @param allEnabled
	 *            Does the set contains all the enabled transitions?
	 */
	public CommonTransitionSet(State state, boolean allEnabled) {
		this.state = state;
		this.transitions = new ArrayList<Transition>();
		this.containingAllEnabled = allEnabled;
	}

	/**
	 * Create a transition set from a given list of transitions.
	 * 
	 * @param state
	 *            The state that all transitions of this set emanate from.
	 * @param transitions
	 *            The list of transitions to initialize the transition set.
	 * @param allEnabled
	 *            Does the set contains all the enabled transitions?
	 */
	public CommonTransitionSet(State state, List<Transition> transitions, boolean allEnabled) {
		this.state = state;
		this.transitions = transitions;
		this.containingAllEnabled = allEnabled;
	}

	@Override
	public int size() {
		return this.transitions.size();
	}

	@Override
	public boolean isEmpty() {
		return this.transitions.isEmpty();
	}

	@Override
	public boolean containsAllEnabled() {
		return this.containingAllEnabled;
	}

	@Override
	public List<Transition> transitions() {
		return transitions;
	}

	@Override
	public void setContainingAllEnabled(boolean value) {
		this.containingAllEnabled = value;
	}

	@Override
	public State source() {
		return state;
	}

	@Override
	public TransitionIterator<State, Transition> randomIterator() {
		// TODO this method will be removed later.
		return null;
	}

	@Override
	public TransitionIterator<State, Transition> iterator() {
		CommonTransitionIterator transitionIterator = new CommonTransitionIterator(this);
		transitionIterator.setOffSet(offSet);

		return transitionIterator;
	}

	@Override
	public Transition get(int i) {
		return transitions.get(i);
	}
	
	@Override
	public boolean hasMultiple() {
		return transitions.size() > 1;
	}
	
	@Override
	public void setOffSet(int offSet) {
		this.offSet = offSet;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(state.toString());
		for (Transition transition : this.transitions) {
			result.append(":\n");
			result.append(transition.toString());
		}
		return result.toString();
	}

}
