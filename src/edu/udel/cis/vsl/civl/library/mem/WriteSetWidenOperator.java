package edu.udel.cis.vsl.civl.library.mem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mem.WriteSetOperations.UnrolledReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * <p>
 * The widen operator <code>widen(loc-set) -> loc</code> for refreshing a group
 * of memory locations<code>loc-set</code>, i.e. the widen operation takes a
 * group of memory locations and returns one memory location which is an
 * over-approximation of the feeding memory location group.
 * </p>
 * 
 * <p>
 * The accuracy of the over-approximation dependes on the implementation of the
 * operator.
 * </p>
 * 
 * @author ziqing
 */
public class WriteSetWidenOperator extends WriteSetOperator {

	WriteSetWidenOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil) {
		super(universe, symbolicUtil);
	}

	@Override
	public Iterable<TreeSet<SymbolicExpression>> apply(
			SymbolicExpression[]... operands) {
		List<SymbolicExpression> pointerSet = new LinkedList<>();

		for (SymbolicExpression operand[] : operands)
			pointerSet.addAll(Arrays.asList(operand));

		List<SimplePointerGroup> groups = grouping(pointerSet);
		TreeSet<SymbolicExpression> ret = new TreeSet<>(universe.comparator());

		for (SimplePointerGroup group : groups)
			ret.addAll(applyWidenOperator(group));
		return Arrays.asList(ret);
	}

	private List<SymbolicExpression> applyWidenOperator(
			SimplePointerGroup group) {
		List<SymbolicExpression> results = new LinkedList<>();
		List<UnrolledReferenceExpression> unrolledMembers = new LinkedList<>();
		ReferenceExpression rootRef = symbolicUtil.getSymRef(group.root);

		for (SymbolicExpression pointer : group.members) {
			ReferenceExpression ref = symbolicUtil.getSymRef(pointer);

			unrolledMembers.add(WriteSetOperations
					.unrolledReferenceExpression(ref, rootRef));
		}

		List<UnrolledReferenceExpression> commonUnrolleds = applyWidenOperatorWorker2(
				unrolledMembers);

		for (UnrolledReferenceExpression unrolled : commonUnrolleds)
			results.add(symbolicUtil.makePointer(group.root,
					rollReferences(unrolled.unrolled)));

		return results;
	}

	private List<UnrolledReferenceExpression> applyWidenOperatorWorker2(
			List<UnrolledReferenceExpression> unrolledReferences) {
		UnrolledReferenceExpression widened = null;

		for (UnrolledReferenceExpression unrolled : unrolledReferences) {
			widened = widened == null
					? unrolled
					: widened.diff(unrolled, universe);
		}
		return Arrays.asList(widened);
	}

	@SuppressWarnings("unused")
	private List<UnrolledReferenceExpression> applyWidenOperatorWorker(
			List<UnrolledReferenceExpression> unrolledReferences) {
		List<List<UnrolledReferenceExpression>> cliques = getCliques(
				unrolledReferences);
		List<UnrolledReferenceExpression> results = new LinkedList<>();

		// TODO: the clique should tell you which positions are different then
		// the following loop can be more efficient:
		for (List<UnrolledReferenceExpression> clique : cliques) {
			UnrolledReferenceExpression common = null;

			for (UnrolledReferenceExpression unrolled : clique) {
				if (common == null) {
					common = unrolled;
					continue;
				}
				common = common.diff(unrolled, universe);
			}
			results.add(common);
		}
		return results;
	}

	private List<List<UnrolledReferenceExpression>> getCliques(
			List<UnrolledReferenceExpression> unrolledReferences) {
		UnrolledReferenceExpression[] unrolleds = new UnrolledReferenceExpression[unrolledReferences
				.size()];
		int numDiffTable[][] = new int[unrolleds.length][unrolleds.length];
		int min = Integer.MAX_VALUE; // 0 < min < MAX_VALUE

		unrolledReferences.toArray(unrolleds);
		for (int i = 0; i < unrolleds.length; i++)
			for (int j = 0; j < unrolleds.length; j++) {
				numDiffTable[i][j] = unrolleds[i].numDiffs(unrolleds[j]);
				if (0 < numDiffTable[i][j] && numDiffTable[i][j] < min)
					min = numDiffTable[i][j];
			}

		BitSet minNeighbors[] = new BitSet[unrolleds.length];

		for (int i = 0; i < unrolleds.length; i++) {
			minNeighbors[i] = new BitSet(unrolleds.length);
			for (int j = 0; j < unrolleds.length; j++)
				if (numDiffTable[i][j] == min)
					minNeighbors[i].set(j);
		}

		List<List<UnrolledReferenceExpression>> results = new LinkedList<>();
		ArrayList<BitSet> allCliques = new ArrayList<>();

		// Bron-Kerbosch algorithm for finding all cliques:
		BitSet vertices = new BitSet(unrolleds.length);
		BitSet result = new BitSet(unrolleds.length);
		BitSet excludes = new BitSet(unrolleds.length);
		int numCliques;

		vertices.flip(0, unrolleds.length);
		bronKerbosch(result, vertices, excludes, minNeighbors, allCliques);
		vertices.clear();
		numCliques = allCliques.size();
		// sorts all cliques by sizes :
		quickSort(0, numCliques, allCliques);
		for (int i = 0; i < numCliques; i++) {
			BitSet clique = allCliques.get(i);

			if (vertices.intersects(clique))
				continue;
			vertices.or(clique);
			results.add(bitset2UnrolledReferences(clique, unrolleds));
		}
		if (vertices.cardinality() != unrolleds.length) {
			for (int i = vertices.nextSetBit(0); i >= 0; i = vertices
					.nextSetBit(i + 1)) {
				List<UnrolledReferenceExpression> singleNodeList = new LinkedList<>();

				singleNodeList.add(unrolleds[i]);
				results.add(singleNodeList);
			}
		}
		return results;
	}

	private List<UnrolledReferenceExpression> bitset2UnrolledReferences(
			BitSet set, UnrolledReferenceExpression[] unrolleds) {
		List<UnrolledReferenceExpression> result = new LinkedList<>();

		for (int i = set.nextSetBit(0); i >= 0; i = set.nextSetBit(i + 1))
			result.add(unrolleds[i]);
		return result;
	}

	/**
	 * Quick sorting {@link BitSet}s by their sizes from larger to smaller.
	 * 
	 * @param low
	 *            lower index of the partition (inclusive)
	 * @param high
	 *            higher index of the partition (exclusive)
	 * @param bitSets
	 *            an {@link ArrayList} of {@link BitSet}s that will be sorted.
	 */
	private void quickSort(int low, int high, ArrayList<BitSet> bitSets) {
		if (high > low) {
			// partition:
			int pivot = high - 1;
			int nextPivot = low - 1;

			for (int j = low; j < high; j++)
				if (bitSets.get(j).cardinality() > bitSets.get(pivot)
						.cardinality())
					swap(bitSets, j, ++nextPivot);
			if (bitSets.get(pivot).cardinality() > bitSets.get(++nextPivot)
					.cardinality())
				swap(bitSets, pivot, nextPivot);
			pivot = nextPivot;
			// recursion
			if (pivot > low)
				quickSort(low, pivot, bitSets);
			else
				return;
			quickSort(pivot, high, bitSets);
		}
	}

	private void swap(ArrayList<BitSet> array, int i, int j) {
		BitSet tmp = array.get(i);

		array.set(i, array.get(j));
		array.set(j, tmp);
	}

	/**
	 * BronKerbosh for finding a clique.
	 */
	private void bronKerbosch(BitSet result, BitSet vertices, BitSet excludes,
			BitSet[] neighborTable, List<BitSet> allResults) {
		if (excludes.isEmpty() && vertices.isEmpty()) {
			allResults.add(result);
			return;
		}
		for (int i = vertices.nextSetBit(0); i >= 0; i = vertices
				.nextSetBit(i + 1)) {
			BitSet newVertices = (BitSet) vertices.clone();
			BitSet newExcludes = (BitSet) excludes.clone();
			BitSet newResult = (BitSet) result.clone();

			newVertices.and(neighborTable[i]);
			newExcludes.and(neighborTable[i]);
			newResult.set(i);
			bronKerbosch(newResult, newVertices, newExcludes, neighborTable,
					allResults);
			vertices.clear(i);
			excludes.set(i);
		}
		return;
	}
}
