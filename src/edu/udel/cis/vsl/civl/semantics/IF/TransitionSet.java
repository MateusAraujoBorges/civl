/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.seq.TransitionSetIF;

/**
 * A transition set contains a list of transitions and the state from which they
 * emanate.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * @author Yihao Yan (yanyihao)
 */
public interface TransitionSet extends TransitionSetIF<State, Transition> {

	/**
	 * Returns true iff this set is empty.
	 * 
	 * @return Returns true iff this set is empty.
	 */
	boolean isEmpty();

	/**
	 * Does this set of transitions contain all enabled transitions of the given
	 * state
	 * 
	 * @return true iff this set of transitions contain all enabled transitions
	 *         of the given state
	 */
	boolean containsAllEnabled();

	/**
	 * @return the set of transitions contained in this set as a list.
	 */
	List<Transition> transitions();

	/**
	 * Sets the flag that denotes if this transition sequence contains all
	 * enabled transitions of the state.
	 */
	void setContainingAllEnabled(boolean value);

	/**
	 * @param i
	 *            The index of the transition
	 * @return the transitions at certain index.
	 */
	Transition get(int i);

	/**
	 * @param offSet
	 *            The value that will be assigned to the offset of a transition
	 *            set.
	 */
	void setOffSet(int offSet);
}
