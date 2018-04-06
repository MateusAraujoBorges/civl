package edu.udel.cis.vsl.civl.library.mem;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;
import java.util.function.Consumer;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mem.WriteSetOperations.UnrolledReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class WriteSetUnionOperator extends WriteSetOperator {

	private GroupRedundantCleaner groupCleaner = null;

	WriteSetUnionOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil) {
		super(universe, symbolicUtil);
		groupCleaner = new GroupRedundantCleaner();
	}

	@Override
	public Iterable<TreeSet<SymbolicExpression>> apply(
			SymbolicExpression[]... operands) {
		assert operands.length == 2;
		List<SymbolicExpression> allPointers = new LinkedList<>();
		List<SimplePointerGroup> groups;
		TreeSet<SymbolicExpression> result = new TreeSet<>(
				universe.comparator());

		for (SymbolicExpression pointer : operands[0])
			allPointers.add(pointer);
		for (SymbolicExpression pointer : operands[1])
			allPointers.add(pointer);
		groups = grouping(allPointers);
		groups.parallelStream().forEach(groupCleaner);
		for (SimplePointerGroup group : groups)
			result.addAll(group.members);
		return Arrays.asList(result);
	}

	/**
	 * For each member <code>p</code> in the given {@link SimplePointerGroup},
	 * if there exist another member <code>q</code> such that <code>p</code>
	 * belongs to <code>q</code>. <code>p</code> is redundant and will be
	 * removed.
	 * 
	 * @param group
	 */
	private void cleanRedundantMembers(SimplePointerGroup group) {
		List<UnrolledReferenceExpression> unrolleds = new LinkedList<>();
		List<UnrolledReferenceExpression> cleanedUnrolleds = new LinkedList<>();
		ReferenceExpression rootRef = symbolicUtil.getSymRef(group.root);

		for (SymbolicExpression member : group.members) {
			if (member.equals(group.root)) {
				group.members.clear();
				group.members.add(group.root);
				return;
			}
			unrolleds.add(WriteSetOperations.unrolledReferenceExpression(
					symbolicUtil.getSymRef(member), rootRef));
		}
		for (UnrolledReferenceExpression unrolled : unrolleds) {
			boolean redundent = false;

			for (UnrolledReferenceExpression member : unrolleds) {
				if (member == unrolled)
					continue;
				if (unrolled.belongto(member)) {
					redundent = true;
					break;
				}
			}
			if (!redundent)
				cleanedUnrolleds.add(unrolled);
		}
		group.members.clear();
		for (UnrolledReferenceExpression unrolled : cleanedUnrolleds)
			group.members.add(symbolicUtil.makePointer(group.root,
					rollReferences(unrolled.unrolled)));
	}

	/**
	 * A class wraps the 'cleanRedundantMembers' method, which is used by
	 * {@link Collection#forEach(Consumer)}
	 * 
	 * @author ziqing
	 */
	private class GroupRedundantCleaner
			implements
				Consumer<SimplePointerGroup> {
		@Override
		public void accept(SimplePointerGroup group) {
			cleanRedundantMembers(group);
		}
	}
}
