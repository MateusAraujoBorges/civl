package edu.udel.cis.vsl.civl.library.mem;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mem.WriteSetOperations.AssignableRefreshment;
import edu.udel.cis.vsl.civl.library.mem.WriteSetOperations.UnrolledReferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;

public class WriteSetRefresher {

	private SymbolicUniverse universe;

	private SymbolicUtility symbolicUtil;

	WriteSetRefresher(SymbolicUniverse universe, SymbolicUtility symbolicUtil) {
		this.universe = universe;
		this.symbolicUtil = symbolicUtil;
	}

	public Pair<State, List<AssignableRefreshment>> refresh(Evaluator evaluator,
			State preState, State state, int pid,
			Iterable<SymbolicExpression> ws, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		List<AssignableRefreshment> results = new LinkedList<>();

		for (SymbolicExpression pointer : ws) {
			Pair<State, AssignableRefreshment> result = refreshWorker(evaluator,
					preState, state, pid, pointer, source);

			state = result.left;
			results.add(result.right);
		}
		return new Pair<>(state, results);
	}

	// preState read only
	private Pair<State, AssignableRefreshment> refreshWorker(
			Evaluator evaluator, State preState, State state, int pid,
			SymbolicExpression pointer, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression oldValue, hvcValue;
		Evaluation eval;
		String process = state.getProcessState(pid).name();
		ReferenceExpression rootRef = symbolicUtil.isPointerToHeap(pointer)
				? symbolicUtil
						.getSymRef(symbolicUtil.getPointer2MemoryBlock(pointer))
				: universe.identityReference();
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		UnrolledReferenceExpression unrolledRef = WriteSetOperations
				.unrolledReferenceExpression(ref, rootRef);
		SymbolicExpression rootPointer = symbolicUtil.makePointer(pointer,
				rootRef);

		// Note: not strict, some "useless" variable may be UNDEFINED at
		// pre-state
		if (unrolledRef.isSingleLocation) {
			eval = evaluator.dereference(source, state, process, pointer, false,
					false);
			eval = evaluator.havoc(state, eval.value.type());
			return new Pair<>(eval.state,
					WriteSetOperations.assignableRefreshment(pointer,
							eval.value, universe.trueExpression()));
		} else
			eval = evaluator.dereference(source, state, process, rootPointer,
					false, false);
		oldValue = eval.value;
		eval.state = state;
		if (oldValue.isNull()) {
			// TODO: SARL NULL maybe can have a type ?
			// the variable is undefined in pre-state, get the type from the
			// current state. Since this location has been written, the
			// dereference should always result in a NON-SARL-NULL object which
			// has a type
			eval = evaluator.dereference(source, state, process, rootPointer,
					false, false);
			eval = evaluator.havoc(state, eval.value.type());
		} else
			eval = evaluator.havoc(state, oldValue.type());
		hvcValue = eval.value;
		state = eval.state;

		/*
		 * constructing assumption components, for widened pointers, which point
		 * to a set of locations,
		 */
		BooleanExpression assumption = universe.trueExpression();
		BooleanExpression clause;
		int boundVarCounter = 0;
		RefreshAssumptionBuilder builder = new RefreshAssumptionBuilder(
				oldValue, hvcValue);

		for (int i = 1; i < unrolledRef.unrolled.length; i++) {
			if (unrolledRef.unrolled[i].isArrayElementReference()) {
				NumericSymbolicConstant newBoundVar = (NumericSymbolicConstant) universe
						.symbolicConstant(
								universe.stringObject(
										"_refresh_i_" + boundVarCounter++),
								universe.integerType());

				builder = refreshArraySlice(
						(ArrayElementReference) unrolledRef.unrolled[i],
						builder, newBoundVar);
			} else
				builder = refreshTupleorUnionField(unrolledRef.unrolled[i],
						builder);

			clause = builder.assumption;
			if (clause.isTrue())
				continue;

			BooleanExpression predicate = universe.equals(builder.oldValue,
					builder.hvcValue);

			predicate = universe.implies(universe.not(clause), predicate);
			for (SymbolicConstant bv : builder.boundVars)
				predicate = universe.forall(bv, predicate);
			assumption = universe.and(assumption, predicate);
		}
		return new Pair<>(state, WriteSetOperations
				.assignableRefreshment(rootPointer, hvcValue, assumption));
	}

	RefreshAssumptionBuilder refreshArraySlice(ArrayElementReference ref,
			RefreshAssumptionBuilder refreshBuilder,
			NumericSymbolicConstant boundVar) {
		SymbolicArrayType arrayType = (SymbolicArrayType) refreshBuilder.hvcValue
				.type();
		BooleanExpression assumption;

		refreshBuilder.oldValue = universe.arrayRead(refreshBuilder.oldValue,
				boundVar);
		refreshBuilder.hvcValue = universe.arrayRead(refreshBuilder.hvcValue,
				boundVar);
		if (UnrolledReferenceExpression.isArraySliceReference(ref)) {
			assumption = universe.lessThanEquals(universe.zeroInt(), boundVar);
			if (arrayType.isComplete()) {
				NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
						.extent();

				assumption = universe.and(assumption,
						universe.lessThan(boundVar, extent));
			}
		} else
			assumption = universe.equals(boundVar, ref.getIndex());
		refreshBuilder.assumption = universe.and(refreshBuilder.assumption,
				assumption);
		refreshBuilder.boundVars.add(boundVar);
		return refreshBuilder;
	}

	RefreshAssumptionBuilder refreshTupleorUnionField(ReferenceExpression ref,
			RefreshAssumptionBuilder refreshBuilder) {
		if (ref.isTupleComponentReference()) {
			IntObject idx = ((TupleComponentReference) ref).getIndex();

			refreshBuilder.oldValue = universe
					.tupleRead(refreshBuilder.oldValue, idx);
			refreshBuilder.hvcValue = universe
					.tupleRead(refreshBuilder.hvcValue, idx);
		}
		if (ref.isUnionMemberReference()) {
			IntObject idx = ((UnionMemberReference) ref).getIndex();

			refreshBuilder.oldValue = universe.unionExtract(idx,
					refreshBuilder.oldValue);
			refreshBuilder.hvcValue = universe.unionExtract(idx,
					refreshBuilder.hvcValue);
		}
		return refreshBuilder;
	}

	private class RefreshAssumptionBuilder {
		SymbolicExpression oldValue;

		SymbolicExpression hvcValue;

		BooleanExpression assumption;

		List<NumericSymbolicConstant> boundVars;

		RefreshAssumptionBuilder(SymbolicExpression oldValue,
				SymbolicExpression hvcValue) {
			this.oldValue = oldValue;
			this.hvcValue = hvcValue;
			this.assumption = universe.trueExpression();
			boundVars = new LinkedList<>();
		}
	}
}
