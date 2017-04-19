package edu.udel.cis.vsl.civl.dynamic.immutable;

import java.util.Comparator;
import java.util.Iterator;
import java.util.TreeSet;

import edu.udel.cis.vsl.civl.dynamic.IF.DynamicWriteSet;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * An immutable pattern implementaion of {@Link DynamicWriteSet}
 * 
 * @author ziqing (Ziqing Luo)
 */
public class ImmutableDynamicWriteSet implements DynamicWriteSet {
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

	/* ***************** public methods from DynamicWriteSet *****************/
	@Override
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

	@Override
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

	@Override
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

	@Override
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
