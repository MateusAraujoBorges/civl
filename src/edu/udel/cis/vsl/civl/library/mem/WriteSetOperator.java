package edu.udel.cis.vsl.civl.library.mem;

import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;

/**
 * The parent class of all write set operators.
 * 
 * @author ziqing
 *
 */
public abstract class WriteSetOperator {

	protected SymbolicUniverse universe;

	protected SymbolicUtility symbolicUtil;

	WriteSetOperator(SymbolicUniverse universe, SymbolicUtility symbolicUtil) {
		this.universe = universe;
		this.symbolicUtil = symbolicUtil;
	}

	/**
	 * Apply an operator on the given write set
	 * 
	 * @param operands
	 *            operands of the operator
	 * @return a set of resulting write sets after the operation. The number of
	 *         resulting write sets depends on the semantics of the operations.
	 */
	public abstract Iterable<TreeSet<SymbolicExpression>> apply(
			SymbolicExpression[]... operands);

	/**
	 * Divide a set of pointers to a set of groups. Pointers that are pointing
	 * to the same Variable will be grouped together.S
	 * 
	 * @param pointers
	 * @return
	 */
	protected List<SimplePointerGroup> grouping(
			Iterable<SymbolicExpression> pointerSet) {
		List<SimplePointerGroup> groups = new LinkedList<>();
		// root -> group
		TreeMap<SymbolicExpression, SimplePointerGroup> groupMap = new TreeMap<>(
				universe.comparator());

		for (SymbolicExpression pointer : pointerSet) {
			if (pointer == symbolicUtil.undefinedPointer())
				continue;

			SymbolicExpression root;
			SimplePointerGroup group;

			if (symbolicUtil.isPointerToHeap(pointer))
				root = symbolicUtil.getPointer2MemoryBlock(pointer);
			else
				root = symbolicUtil.makePointer(pointer,
						universe.identityReference());
			group = groupMap.get(root);
			if (group == null) {
				group = new SimplePointerGroup(root);
				groupMap.put(root, group);
			}
			group.members.add(pointer);
		}
		for (SimplePointerGroup group : groupMap.values())
			groups.add(group);
		return groups;
	}

	protected ReferenceExpression rollReferences(
			ReferenceExpression[] unrolledRefs) {
		ReferenceExpression ret = unrolledRefs[0];

		for (int i = 1; i < unrolledRefs.length; i++)
			ret = wrap(unrolledRefs[i], ret);
		return ret;
	}

	private ReferenceExpression wrap(ReferenceExpression parent,
			ReferenceExpression child) {
		switch (parent.referenceKind()) {
			case ARRAY_ELEMENT :
				return universe.arrayElementReference(child,
						((ArrayElementReference) parent).getIndex());
			case TUPLE_COMPONENT :
				return universe.tupleComponentReference(child,
						((TupleComponentReference) parent).getIndex());
			case UNION_MEMBER :
				return universe.unionMemberReference(child,
						((UnionMemberReference) parent).getIndex());
			default :
				assert false;
		}
		return null;
	}

	/**
	 * A group of memory locations that belongs to the same Variable (or a heap
	 * object created by the same <code>malloc</code> instance).
	 * 
	 * @author ziqing
	 */
	protected class SimplePointerGroup {
		protected final SymbolicExpression root;

		protected TreeSet<SymbolicExpression> members;

		SimplePointerGroup(SymbolicExpression root) {
			this.root = root;
			this.members = new TreeSet<>(universe.comparator());
		}
	}
}
