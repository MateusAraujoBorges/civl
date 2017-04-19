package edu.udel.cis.vsl.civl.dynamic.immutable;

import java.util.Comparator;
import java.util.Iterator;
import java.util.TreeSet;

import edu.udel.cis.vsl.civl.library.civlc.LibcivlcExecutor;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiExecutor;
import edu.udel.cis.vsl.civl.library.time.LibtimeExecutor;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.common.CommonExecutor;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableStateFactory;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * <p>
 * This class represents a write set value which is formed dynamically. A
 * dynamic write set stores a set of memory location references which refer to
 * the memory locations that are changed ( from a point that starts monitoring
 * "write" operations).
 * 
 * An instance of this class is a referenced value for a {@link Variable} with
 * $mem type.
 *
 * </p>
 * 
 * <p>
 * <b>Here is just a record of Java methods, calling of which will change the
 * write set</b>
 * <ul>
 * <li>The proctected method {@link CommonExecutor#assign}s, there are two of
 * them.</li>
 * <li>
 * {@link ImmutableStateFactory#deallocate(edu.udel.cis.vsl.civl.state.IF.State, SymbolicExpression, int, int, int)}
 * </li>
 * <li>
 * {@link ImmutableStateFactory#malloc(edu.udel.cis.vsl.civl.state.IF.State, int, int, SymbolicExpression)}
 * </li> TODO: can all the following go through the executor's assign() ?
 * <li>{@link LibmpiExecutor#executeNewGcomm} (TODO: is this needed to be
 * recorded ?)</li>
 * <li>{@link LibtimeExecutor#executeLocalTime}</li>
 * <li>{@link CommonExecutor#executeNextInDomain} (TODO: this one needs some
 * special non-concretet handling)</li>
 * <li>{@link LibcivlcExecutor#executeNextTimeCount}</li>
 * </ul>
 * </p>
 * 
 * @author ziqing (Ziqing Luo)
 */
public class ImmutableDynamicWriteSet implements Iterable<SymbolicExpression> {
	/**
	 * A collection of references (pointers) to memroy locations (objects). For
	 * each reference, there is an initial value associates to it.
	 */
	private TreeSet<SymbolicExpression> pointerSet = null;

	private boolean canonicalized = false;

	public ImmutableDynamicWriteSet(SymbolicUniverse universe) {
		pointerSet = new TreeSet<>(universe.comparator());
	}

	@SuppressWarnings("unchecked")
	private ImmutableDynamicWriteSet(Comparator<?> comparator) {
		this.pointerSet = (TreeSet<SymbolicExpression>) new TreeSet<>(
				comparator);
	}

	private ImmutableDynamicWriteSet(TreeSet<SymbolicExpression> references) {
		this.pointerSet = new TreeSet<>(references);
	}

	// *********************** public methods: ***********************
	/**
	 * <p>
	 * Add a set of memory location references to the write set
	 * </p>
	 * 
	 * @param pointer
	 *            A set of {@link SymbolicExpression} which represents a set of
	 *            concrete pointer.
	 * @return A new instance if the pointer is not in this write set; otherwise
	 *         return this instance.
	 */
	public ImmutableDynamicWriteSet addReference(SymbolicExpression pointer) {
		assert pointer.operator() == SymbolicOperator.TUPLE;
		if (pointerSet.contains(pointer)) {
			return this;
		} else {
			ImmutableDynamicWriteSet newSet = new ImmutableDynamicWriteSet(
					this.pointerSet);

			newSet.pointerSet.add(pointer);
			return newSet;
		}
	}

	/**
	 * <p>
	 * Canonicalize all memory location references in this write set.
	 * </p>
	 * 
	 * @param universe
	 *            An instance of {@link SymbolicUniverse}
	 * @return A new instance whose references are canonic ones of this.
	 */
	public ImmutableDynamicWriteSet canonicalize(SymbolicUniverse universe) {
		if (canonicalized)
			return this;

		ImmutableDynamicWriteSet newSet = new ImmutableDynamicWriteSet(
				universe);

		for (SymbolicExpression pointer : pointerSet)
			newSet.pointerSet.add(universe.canonic(pointer));
		newSet.canonicalized = true;
		return newSet;

	}

	/**
	 * <p>
	 * Apply an {@link UnaryOperator} on the set of memory location references.
	 * If the operator changes nothing, return this instance.
	 * </p>
	 * 
	 * @param operator
	 * @return A new instance whose references are obtained by applying the
	 *         operator on ones of this
	 */
	public ImmutableDynamicWriteSet apply(
			UnaryOperator<SymbolicExpression> operator) {
		ImmutableDynamicWriteSet newSet = new ImmutableDynamicWriteSet(
				pointerSet.comparator());
		boolean change = false;

		for (SymbolicExpression pointer : pointerSet) {
			SymbolicExpression newPointer = operator.apply(pointer);

			newSet.pointerSet.add(newPointer);
			if (!change && newPointer != pointer)
				change = true;
		}
		if (change)
			return newSet;
		else
			return this;
	}

	/**
	 * <p>
	 * Simplify the reference set using the given {@link Reasoner}.
	 * </p>
	 * 
	 * @param reasoner
	 *            An instance of a {@link Reasoner}.
	 * @return A new {@link ImmutableDynamicWriteSet} instance whose symbolic
	 *         contents are simplified.
	 */
	public ImmutableDynamicWriteSet simplify(Reasoner reasoner) {
		ImmutableDynamicWriteSet newSet = new ImmutableDynamicWriteSet(
				pointerSet.comparator());
		boolean change = false;

		for (SymbolicExpression pointer : pointerSet) {
			SymbolicExpression newPointer = reasoner.simplify(pointer);

			newSet.pointerSet.add(newPointer);
			if (!change && newPointer != pointer)
				change = true;
		}
		if (change)
			return newSet;
		else
			return this;
	}

	/* ***************** Public methods from Objects ******************* */

	@Override
	public String toString() {
		String result = "";

		for (SymbolicExpression entry : pointerSet)
			result += entry + " \n";
		return result;
	}

	@Override
	public int hashCode() {
		int hashCode = pointerSet.size();

		for (SymbolicExpression entry : pointerSet)
			hashCode ^= entry.hashCode();
		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof ImmutableDynamicWriteSet) {
			ImmutableDynamicWriteSet other = (ImmutableDynamicWriteSet) obj;

			return other.pointerSet.equals(pointerSet);
		}
		return false;
	}

	/* ***************** Public methods from Iterable ******************* */
	@Override
	public Iterator<SymbolicExpression> iterator() {
		return pointerSet.iterator();
	}
}
