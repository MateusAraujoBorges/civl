package edu.udel.cis.vsl.civl.library.mem;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.function.Function;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.OffsetReference;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression.ReferenceKind;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class WriteSetOperations {
	/* ************************* sub-classes *****************************/

	public static class AssignableRefreshment {

		public final SymbolicExpression pointer;

		public final SymbolicExpression refreshedObject;

		public final BooleanExpression assumption;

		private AssignableRefreshment(SymbolicExpression pointer,
				SymbolicExpression refreshedObject,
				BooleanExpression assumption) {
			this.pointer = pointer;
			this.refreshedObject = refreshedObject;
			this.assumption = assumption;
		}
	}

	public static class UnrolledReferenceExpression {

		private static final String ARRAY_SLICE_WILDCARD_INDEX_NAME = "$widen_wildcard";

		private static NumericExpression ARRAY_SLICE_WILDCARD_INDEX = null;

		public final boolean isSingleLocation;

		public final ReferenceExpression[] unrolled;

		public UnrolledReferenceExpression(ReferenceExpression ref,
				ReferenceExpression rootRef) {
			LinkedList<ReferenceExpression> unrolledList = new LinkedList<>();
			boolean isSingleLocation = true;

			while (ref != rootRef) {
				if (isSingleLocation && isArraySliceReference(ref))
					isSingleLocation = false;
				unrolledList.addFirst(ref);
				ref = ((NTReferenceExpression) ref).getParent();
			}
			unrolledList.addFirst(ref);
			unrolled = new ReferenceExpression[unrolledList.size()];
			unrolledList.toArray(unrolled);
			this.isSingleLocation = isSingleLocation;
		}

		private UnrolledReferenceExpression(ReferenceExpression[] unrolled) {
			Boolean isSingleLocation = true;

			for (int i = 0; i < unrolled.length; i++)
				if (isArraySliceReference(unrolled[i])) {
					isSingleLocation = false;
					break;
				}
			this.unrolled = unrolled;
			this.isSingleLocation = isSingleLocation;
		}

		static public ReferenceExpression arraySliceReference(
				ReferenceExpression arrayRef, SymbolicUniverse universe) {
			if (ARRAY_SLICE_WILDCARD_INDEX == null)
				ARRAY_SLICE_WILDCARD_INDEX = (NumericExpression) universe
						.symbolicConstant(
								universe.stringObject(
										ARRAY_SLICE_WILDCARD_INDEX_NAME),
								universe.integerType());
			return universe.arrayElementReference(arrayRef,
					ARRAY_SLICE_WILDCARD_INDEX);
		}

		static public boolean isArraySliceReference(ReferenceExpression ref) {
			if (ref.isArrayElementReference())
				return ((ArrayElementReference) ref)
						.getIndex() == ARRAY_SLICE_WILDCARD_INDEX;
			return false;
		}

		// unrolled[index] must be an array element reference:
		public UnrolledReferenceExpression replaceWithArraySliceReference(
				SymbolicUniverse universe, int index) {
			ReferenceExpression newRef = arraySliceReference(
					unrolled[index - 1], universe);
			ReferenceExpression[] newUnrolled = Arrays.copyOf(unrolled,
					unrolled.length);

			newUnrolled[index] = newRef;
			return new UnrolledReferenceExpression(newUnrolled);
		}

		/**
		 * <p>
		 * Return the common part of two unrolled reference expressions. For
		 * different part at position <code>i</code> of the unrolled reference
		 * expression array, <code>i</code> will be left as "java null". The
		 * returned array has no "java null" suffix.
		 * </p>
		 * 
		 * <p>
		 * Over-approximations: if there exists other kinds of reference
		 * expressions than ARRAY_ELEMENT, in position <code>i</code> of the
		 * unrolled reference expression array, all references from
		 * <code>i</code> to the end will be considered as different and need
		 * get refreshed.
		 * </p>
		 */
		public UnrolledReferenceExpression diff(
				UnrolledReferenceExpression other, SymbolicUniverse universe) {
			int min = unrolled.length < other.unrolled.length
					? unrolled.length
					: other.unrolled.length;
			ReferenceExpression[] ret = new ReferenceExpression[min];

			for (int i = 0; i < min; i++) {
				if (!shallowEqual(unrolled[i], other.unrolled[i])) {
					ret[i] = null;
				} else
					ret[i] = unrolled[i];
			}
			// trim null suffix:
			for (int i = ret.length - 1; i >= 0; i--)
				if (ret[i] != null) {
					for (int j = 1; j < i; j++)
						if (ret[j] == null)
							ret[j] = arraySliceReference(ret[j - 1], universe);
					return new UnrolledReferenceExpression(
							Arrays.copyOfRange(ret, 0, i + 1));
				}
			return new UnrolledReferenceExpression(new ReferenceExpression[0]);
		}

		public int numDiffs(UnrolledReferenceExpression other) {
			int min = unrolled.length, max = other.unrolled.length;
			int numDiff;

			if (min > max) {
				min = max;
				max = unrolled.length;
			}
			numDiff = max - min;
			for (int i = 0; i < min; i++)
				if (!shallowEqual(unrolled[i], other.unrolled[i]))
					numDiff++;
			return numDiff;
		}

		/**
		 * @param that
		 * @return true iff this unrolled reference expression "belongs to" that
		 *         unrolled reference expression, i.e.
		 *         <ol>
		 *         <li>this must have the unrolled length <code>l</code> greater
		 *         than or equal to that unrolled length</li>
		 *         <li>for every i-th element in this unrolled references
		 *         <code>(0 &lt= i &lt l)</code>, it must either equals to the
		 *         i-th element in that unrolled references or the i-th element
		 *         in that unrolled references is
		 *         {@link WriteSetOperations#ARRAY_SLICE_WILDCARD_INDEX}</li>
		 *         </ol>
		 */
		public boolean belongto(UnrolledReferenceExpression that) {
			ReferenceExpression thisUnrolled[] = this.unrolled;

			if (thisUnrolled.length > that.unrolled.length)
				thisUnrolled = Arrays.copyOfRange(thisUnrolled, 0,
						that.unrolled.length);
			if (thisUnrolled.length == that.unrolled.length) {
				for (int i = 0; i < thisUnrolled.length; i++) {
					if (!shallowEqual(thisUnrolled[i], that.unrolled[i])) {
						if (!isArraySliceReference(that.unrolled[i]))
							return false;
					}
				}
				return true;
			}
			return false;
		}

		private boolean shallowEqual(ReferenceExpression r0,
				ReferenceExpression r1) {
			ReferenceKind kind = r0.referenceKind();

			assert kind == r1.referenceKind();
			switch (kind) {
				case ARRAY_ELEMENT :
					return ((ArrayElementReference) r0).getIndex()
							.equals(((ArrayElementReference) r1).getIndex());
				case OFFSET :
					return ((OffsetReference) r0).getOffset()
							.equals(((OffsetReference) r1).getOffset());
				case TUPLE_COMPONENT :
					return ((TupleComponentReference) r0).getIndex()
							.equals(((TupleComponentReference) r1).getIndex());
				case UNION_MEMBER :
					return ((UnionMemberReference) r0).getIndex()
							.equals(((UnionMemberReference) r1).getIndex());
				case IDENTITY :
				case NULL :
				default :
					return true;
			}
		}
	}

	/*
	 * ************************** public methods **************************
	 */

	static public AssignableRefreshment assignableRefreshment(
			SymbolicExpression pointer, SymbolicExpression refreshedObject,
			BooleanExpression assumption) {
		return new AssignableRefreshment(pointer, refreshedObject, assumption);
	}

	static public UnrolledReferenceExpression unrolledReferenceExpression(
			ReferenceExpression ref, ReferenceExpression rootRef) {
		return new UnrolledReferenceExpression(ref, rootRef);
	}

	static public WriteSetWidenOperator widenOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil) {
		return new WriteSetWidenOperator(universe, symbolicUtil);
	}

	static public WriteSetUnionOperator unionOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil) {
		return new WriteSetUnionOperator(universe, symbolicUtil);
	}

	static public WriteSetGroupOperator groupOperator(SymbolicUniverse universe,
			SymbolicUtility symbolicUtil,
			Function<SymbolicExpression, IntegerNumber> scopeValueToKey) {
		return new WriteSetGroupOperator(universe, symbolicUtil,
				scopeValueToKey);
	}

	static public WriteSetRefresher dynamicWriteSetRefresher(
			SymbolicUniverse universe, SymbolicUtility symbolicUtil) {
		return new WriteSetRefresher(universe, symbolicUtil);
	}
}
