package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;

public class ErrorSideEffectFreeEvaluator extends CommonEvaluator
		implements
			Evaluator {

	public ErrorSideEffectFreeEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, MemoryUnitFactory memUnitFactory,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, loaderExec, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
	}

	@Override
	Evaluation dereference(CIVLSource source, State state, String process,
			CIVLType resultType, SymbolicExpression pointer,
			boolean checkOutput, boolean analysisOnly, boolean strict)
			throws UnsatisfiablePathConditionException {
		boolean throwPCException = false;
		SymbolicExpression deref = null;

		// C11 6.5.3.2: If an invalid value has been assigned to the
		// pointer, the behavior of the unary * operator is undefined.
		//
		// footnote: Among the invalid values for dereferencing a pointer by
		// the unary * operator are a null pointer, an address
		// inappropriately aligned for the type of object pointed to, and
		// the address of an object after the end of its lifetime.
		if (!pointer.type().equals(this.pointerType)
				|| pointer.operator() != SymbolicOperator.TUPLE
				|| symbolicUtil.isNullPointer(pointer)) {

			deref = modelFactory
					.undefinedValue(resultType.getDynamicType(universe));
			return new Evaluation(state, deref);
		} else {
			int sid = symbolicUtil.getDyscopeId(source, pointer);

			if (sid == ModelConfiguration.DYNAMIC_REMOVED_SCOPE) {
				deref = modelFactory
						.undefinedValue(resultType.getDynamicType(universe));
				return new Evaluation(state, deref);
			} else {
				ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);
				SymbolicExpression variableValue;
				int vid = symbolicUtil.getVariableId(source, pointer);

				if (sid == ModelConfiguration.DYNAMIC_CONSTANT_SCOPE) {
					variableValue = this.modelFactory.model()
							.staticConstantScope().variable(vid)
							.constantValue();
				} else {
					if (!analysisOnly && checkOutput) {
						Variable variable = state.getDyscope(sid).lexicalScope()
								.variable(vid);

						if (variable.isOutput()) {
							errorLogger.logSimpleError(source, state, process,
									symbolicAnalyzer.stateInformation(state),
									ErrorKind.OUTPUT_READ,
									"Attempt to read output variable "
											+ variable.name().name());
							throwPCException = true;
						}
					}
					variableValue = state.getDyscope(sid).getValue(vid);
				}
				try {
					deref = universe.dereference(variableValue, symRef);
				} catch (SARLException e) {
					errorLogger.logSimpleError(source, state, process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.DEREFERENCE,
							"Illegal pointer dereference: " + e.getMessage()
									+ "\n"
									+ symbolicAnalyzer.stateInformation(state));
					throwPCException = true;
				}
			}
		}
		if (throwPCException)
			throw new UnsatisfiablePathConditionException();
		else
			return new Evaluation(state, deref);
	}

	@Override
	protected Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.pointer());

		if (eval.value.isNull()) {
			// C11 6.5.3.2: If an invalid value has been assigned to the
			// pointer, the behavior of the unary * operator is undefined.
			//
			// footnote: Among the invalid values for dereferencing a pointer by
			// the unary * operator are a null pointer, an address
			// inappropriately aligned for the type of object pointed to, and
			// the address of an object after the end of its lifetime.
			eval.value = modelFactory.undefinedValue(
					expression.getExpressionType().getDynamicType(universe));
			return eval;
		}
		return dereference(expression.pointer().getSource(), eval.state,
				process, expression.getExpressionType(), eval.value, true,
				true);
	}

	@Override
	protected Evaluation evaluateSubscript(State state, int pid, String process,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, expression.array());
		SymbolicExpression array = eval.value;
		NumericExpression index;

		eval = evaluate(state, pid, expression.index());
		index = (NumericExpression) eval.value;
		eval.value = universe.arrayRead(array, index);
		return eval;
	}

	@Override
	protected Pair<Evaluation, NumericExpression[]> pointerAddWorker(
			State state, int pid, SymbolicExpression pointer,
			NumericExpression offset, boolean checkOutput, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression arrayPtr;
		ReferenceExpression parentRef;
		NumericExpression extent, index;
		ReferenceExpression ref;
		ReferenceExpression newRef;
		BooleanExpression claim;
		BooleanExpression gteUpper;
		BooleanExpression ltLower;
		Evaluation eval;
		int scopeId, vid;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		ResultType resultType = null;
		String process = state.getProcessState(pid).name();

		claim = universe.equals(offset, zero);
		if (reasoner.isValid(claim))
			return new Pair<>(new Evaluation(state, pointer), null);
		scopeId = symbolicUtil.getDyscopeId(source, pointer);
		vid = symbolicUtil.getVariableId(source, pointer);
		ref = symbolicUtil.getSymRef(pointer);
		// Checking if the pointer addition will be out of bound at the current
		// dimension.
		assert ref.isArrayElementReference();
		arrayPtr = symbolicUtil.parentPointer(pointer);
		index = ((ArrayElementReference) ref).getIndex();
		eval = dereference(source, state, process, null, arrayPtr, false, true);
		state = eval.state;

		SymbolicArrayType arrayType = (SymbolicArrayType) eval.value.type();

		if (!arrayType.isComplete()) {
			return new Pair<>(
					new Evaluation(state,
							symbolicUtil.makePointer(pointer,
									universe.offsetReference(ref, offset))),
					null);
		}
		extent = ((SymbolicCompleteArrayType) eval.value.type()).extent();
		// higher than the upper bound
		gteUpper = universe.lessThanEquals(extent, universe.add(index, offset));
		// lower than the lower bound
		ltLower = universe.lessThan(universe.add(index, offset), zero);
		// Conditions of recomputing array indices:
		// If the pointer points to an element of an array object and it can be
		// proved that the result of the pointer addition will point to other
		// sub-arrays.
		if (!symbolicUtil.isHeapObjectPointer(pointer))
			if (symbolicUtil.getSymRef(arrayPtr).isArrayElementReference()) {
				resultType = reasoner.valid(universe.or(gteUpper, ltLower))
						.getResultType();
				if (resultType == ResultType.YES)
					return recomputeArrayIndices(state, pid, vid, scopeId,
							pointer, offset, reasoner, source);
			}
		parentRef = symbolicUtil.getSymRef(arrayPtr);
		newRef = universe.arrayElementReference(parentRef,
				universe.add(index, offset));
		eval = new Evaluation(state,
				symbolicUtil.makePointer(scopeId, vid, newRef));
		return new Pair<>(eval, null);
	}

	@Override
	protected Evaluation evaluateDivide(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression result;
		BooleanExpression denoEqZero = universe.equals(denominator, zero);

		if (denominator.isZero() || universe.reasoner(state.getPathCondition())
				.isValid(denoEqZero))
			result = modelFactory.undefinedValue(
					expression.getExpressionType().getDynamicType(universe));
		result = universe.divide((NumericExpression) numerator, denominator);
		return new Evaluation(state, result);
	}

	@Override
	protected Pair<Evaluation, NumericExpression[]> recomputeArrayIndices(
			State state, int pid, int pointedVid, int pointedSid,
			SymbolicExpression pointer, NumericExpression offset,
			Reasoner reasoner, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression newIndex, totalOffset = zero;
		NumericExpression sliceSize = one;
		SymbolicExpression arrayRootPtr;
		NumericExpression[] indices, coordinateSizes, sliceSizes, oldIndices;
		ReferenceExpression newRef;
		Evaluation eval;
		int dim;
		CIVLType arrayType;
		SymbolicCompleteArrayType dyarrayType;
		TypeEvaluation teval;

		arrayRootPtr = symbolicUtil.arrayRootPtr(pointer);
		arrayType = symbolicAnalyzer.typeOfObjByPointer(source, state,
				arrayRootPtr);
		assert arrayType.isArrayType()
				&& ((CIVLArrayType) arrayType).isComplete();
		teval = getDynamicType(state, pid, arrayType, source, false);
		assert teval.type instanceof SymbolicArrayType
				&& ((SymbolicArrayType) teval.type).isComplete();
		dyarrayType = (SymbolicCompleteArrayType) teval.type;
		state = teval.state;
		coordinateSizes = symbolicUtil.arrayDimensionExtents(dyarrayType);
		sliceSizes = symbolicUtil.arraySlicesSizes(coordinateSizes);
		dim = dyarrayType.dimensions();
		oldIndices = symbolicUtil.extractArrayIndicesFrom(pointer);
		assert oldIndices.length <= dim && sliceSizes.length == dim;
		// computes total offset from the first element
		for (int i = 0; i < oldIndices.length; i++) {
			NumericExpression oldIndex;

			oldIndex = oldIndices[i];
			sliceSize = sliceSizes[i];
			totalOffset = universe.add(totalOffset,
					universe.multiply(oldIndex, sliceSize));
		}
		totalOffset = universe.add(totalOffset, offset);
		// Computes new indexes
		indices = new NumericExpression[dim];
		for (int i = 0; i < dim; i++) {
			BooleanExpression checkClaim;
			ResultType checkResultType;
			Pair<NumericExpression, NumericExpression> newIndex_remainder;

			sliceSize = sliceSizes[i];
			newIndex_remainder = symbolicUtil.arithmeticIntDivide(totalOffset,
					sliceSize);
			newIndex = newIndex_remainder.left;
			totalOffset = newIndex_remainder.right;
			checkClaim = universe.lessThan(newIndex, coordinateSizes[i]);
			checkResultType = reasoner.valid(checkClaim).getResultType();
			if (!checkResultType.equals(ResultType.YES)) {
				BooleanExpression equalExtentClaim = universe.equals(newIndex,
						coordinateSizes[i]);

				checkResultType = reasoner.valid(equalExtentClaim)
						.getResultType();
				if (checkResultType.equals(ResultType.YES)) {
					if (i < dim - 1) {
						newIndex = universe.subtract(newIndex, one);
						totalOffset = universe.add(totalOffset, sliceSizes[i]);
					}
				}
			}
			indices[i] = newIndex;
		}
		newRef = symbolicUtil.makeArrayElementReference(
				symbolicUtil.getSymRef(arrayRootPtr), indices);
		eval = new Evaluation(state,
				symbolicUtil.makePointer(pointedSid, pointedVid, newRef));
		return new Pair<>(eval, sliceSizes);
	}
}
