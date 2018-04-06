package edu.udel.cis.vsl.civl.library.mem;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLScopeType;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class WriteSetGroupOperator extends WriteSetOperator {

	/**
	 * A function that is provided by
	 * {@link CIVLScopeType#scopeValueToIdentityOperator(SymbolicUniverse)}
	 * which extracts a key from a concrete scope value.
	 */
	protected Function<SymbolicExpression, IntegerNumber> scopeValueToKey;

	WriteSetGroupOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil,
			Function<SymbolicExpression, IntegerNumber> scopeValueToKey) {
		super(universe, symbolicUtil);
		this.scopeValueToKey = scopeValueToKey;
	}

	@Override
	public Iterable<TreeSet<SymbolicExpression>> apply(
			SymbolicExpression[]... operands) {
		List<SymbolicExpression> pointerSet = new LinkedList<>();
		List<TreeSet<SymbolicExpression>> results = new LinkedList<>();

		for (int i = 0; i < operands.length; i++)
			for (SymbolicExpression ptr : operands[i])
				pointerSet.add(ptr);
		for (SimplePointerGroup group : grouping(pointerSet))
			results.add(group.members);
		return results;
	}

	public int numGroups(SymbolicExpression[] pointers) {
		Set<Integer> counter = new TreeSet<>();
		int[] key = new int[2];

		for (SymbolicExpression pointer : pointers) {
			key[0] = scopeValueToKey.apply(symbolicUtil.getScopeValue(pointer))
					.intValue();
			key[1] = scopeValueToKey.apply(symbolicUtil.getScopeValue(pointer))
					.intValue();

			counter.add(Arrays.hashCode(key));
		}
		return counter.size();
	}

	public SymbolicExpression[] getGroup(SymbolicExpression[] pointers,
			SymbolicExpression root) {
		List<SymbolicExpression> result = new LinkedList<>();

		for (SymbolicExpression pointer : pointers) {
			SymbolicExpression rootOfPointer = symbolicUtil
					.isPointerToHeap(pointer)
							? symbolicUtil.getPointer2MemoryBlock(pointer)
							: symbolicUtil.makePointer(pointer,
									universe.identityReference());
			if (rootOfPointer.equals(root))
				result.add(pointer);
		}

		SymbolicExpression[] resultToArray = new SymbolicExpression[result
				.size()];

		return result.toArray(resultToArray);
	}
}
