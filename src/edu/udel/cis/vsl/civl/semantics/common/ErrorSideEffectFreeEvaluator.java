package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An error side-effects free alternative of {@link CommonEvaluator}. This
 * evaluator will not report errors for error side-effects during the
 * evaluation.
 * 
 * @author ziqingluo
 *
 */
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
	public Evaluation dereference(CIVLSource source, State state,
			String process, SymbolicExpression pointer, boolean checkOutput,
			boolean strict) throws UnsatisfiablePathConditionException {
		boolean muteErrorSideEffects = true; // mute error side effects

		return dereferenceWorker(source, state, process, pointer, checkOutput,
				false, strict, muteErrorSideEffects);
	}

	@Override
	protected Evaluation evaluateSubscript(State state, int pid, String process,
			SubscriptExpression expression)
			throws UnsatisfiablePathConditionException {
		return evaluateSubscriptWorker(state, pid, process, expression, true);
	}

	@Override
	protected Evaluation evaluateDivide(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator)
			throws UnsatisfiablePathConditionException {
		return evaluateDivideWorker(state, pid, expression, numerator,
				denominator, true);
	}

	@Override
	protected Evaluation evaluateModulo(State state, int pid,
			BinaryExpression expression, NumericExpression numerator,
			NumericExpression denominator)
			throws UnsatisfiablePathConditionException {
		return evaluateModuloWorker(state, pid, expression, numerator,
				denominator, true);
	}

	@Override
	public Pair<Evaluation, NumericExpression[]> arrayElementReferenceAdd(State state,
			int pid, SymbolicExpression ptr, NumericExpression offset,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression newPtr = symbolicUtil.makePointer(ptr,
				symbolicAnalyzer.getLeafNodeReference(state, ptr, source));

		return arrayElementReferenceAddWorker(state, pid, newPtr, offset, true,
				source);
	}

	@Override
	public Evaluation evaluatePointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException {
		Pair<BooleanExpression, ResultType> checkPointer = symbolicAnalyzer
				.isDefinedPointer(state, pointer, expression.getSource());

		if (checkPointer.right != ResultType.YES)
			return new Evaluation(state, symbolicUtil.undefinedPointer());
		else {
			ReferenceExpression symRef = symbolicUtil.getSymRef(pointer);

			if (symRef.isArrayElementReference()) {
				return arrayElementReferenceAddWorker(state, pid, pointer,
						offset, true, expression.left().getSource()).left;
			} else if (symRef.isOffsetReference()) {
				return offsetReferenceAddition(state, pid, pointer, offset,
						true, expression.getSource());
			} else if (symRef.isIdentityReference()) {
				return identityReferenceAddition(state, pid, pointer, offset,
						true, expression.getSource());
			} else
				throw new CIVLUnimplementedFeatureException(
						"Pointer addition for anything other than array elements or variables",
						expression);
		}
	}
}
