package edu.udel.cis.vsl.civl.semantics.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.TransitionIteratorIF;

/**
 * A transition set contains a list of transitions and the state from which
 * they emanate.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 */
public class CommonTransitionSet implements TransitionSet {

	/* *************************** Instance Fields ************************* */

	/**
	 * All the transitions emanating from a certain state.
	 */
	private List<Transition> transitions;

	/**
	 * This is the state from which all the transitions in the sequence emanate.
	 */
	private State state;

	/**
	 * The number of elements executed from this set since it is created.
	 */
	private int numExecuted = 0;

	private boolean containingAllEnabled = false;

	/* ***************************** Constructors ************************** */

	/**
	 * Create an empty transition set.
	 * 
	 * @param state
	 *            The state that all transitions of this set emanate from.
	 */
	public CommonTransitionSet(State state, boolean allEnabled) {
		this.state = state;
		this.transitions = new ArrayList<Transition>();
		this.containingAllEnabled = allEnabled;
	}

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
	public TransitionIteratorIF<State, Transition> randomIterator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TransitionIteratorIF<State, Transition> iterator() {
		return new CommonTransitionIterator(this);
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
	public int numExecuted() {
		return numExecuted;
	}
	
	@Override
	public void incrementNumExecuted(){
		numExecuted++;
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
