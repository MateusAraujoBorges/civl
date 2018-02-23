package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.ACSLPredicateCall;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
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
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

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

	/**
	 * The {@link Exception} that will be thrown only by
	 * {@link ErrorSideEffectFreeEvaluator} when an erroneous side effect
	 * happens.
	 * 
	 * @author ziqing
	 */
	static public class ErroneousSideEffectException
			extends
				UnsatisfiablePathConditionException {
		/**
		 * The {@link SymbolicExpression} that really causes the side effect
		 * error, which will be used to as a key for generating a unique
		 * undefined value
		 */
		public final SymbolicExpression keyValue;
		/**
		 * generated serial ID
		 */
		private static final long serialVersionUID = -1237052183722755533L;

		/**
		 * @param keyValue
		 *            The {@link SymbolicExpression} that really causes the side
		 *            effect error, which will be used to as a key for
		 *            generating a unique undefined value
		 */
		public ErroneousSideEffectException(SymbolicExpression keyValue) {
			this.keyValue = keyValue;
		}
	}

	/**
	 * The name of an abstract function which will wrap a
	 * {@link ErroneousSideEffectException#keyValue}. A such function call
	 * represents a unique undefined value of some type.
	 */
	private static String SEError_ABSTRACT_FUNCTION_NAME = "SEError_undefined";

	public ErrorSideEffectFreeEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, MemoryUnitFactory memUnitFactory,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, loaderExec, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		try {
			switch (expression.expressionKind()) {
				case ACSL_PREDICATE_CALL :
					return evaluateACSLPredicateCall(state, pid,
							(ACSLPredicateCall) expression);
				default :
					return super.evaluate(state, pid, expression);
			}
		} catch (ErroneousSideEffectException e) {
			SymbolicType exprType = expression.getExpressionType()
					.getDynamicType(universe);
			SymbolicFunctionType funcType = universe
					.functionType(Arrays.asList(e.keyValue.type()), exprType);

			return new Evaluation(state, universe.apply(
					universe.symbolicConstant(universe.stringObject(
							SEError_ABSTRACT_FUNCTION_NAME), funcType),
					Arrays.asList(e.keyValue)));
		}
	}

	@Override
	public Evaluation dereference(CIVLSource source, State state,
			String process, CIVLType referredType, SymbolicExpression pointer,
			boolean checkOutput, boolean strict)
			throws UnsatisfiablePathConditionException {
		boolean muteErrorSideEffects = true; // mute error side effects

		return dereferenceWorker(source, state, process, referredType, pointer,
				checkOutput, false, strict, muteErrorSideEffects);
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
	public Pair<Evaluation, NumericExpression[]> arrayElementReferenceAdd(
			State state, int pid, SymbolicExpression ptr,
			NumericExpression offset, CIVLSource source)
			throws UnsatisfiablePathConditionException {
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

	/**
	 * <p>
	 * An {@link ACSLPredicateCall} evaluates to an symbolic expression of
	 * {@link SymbolicOperator#APPLY} operator. Actual parameters are applied to
	 * a symbolic constant which represents the ACSL predicate function.
	 * </p>
	 * 
	 * @param state
	 * @param pid
	 * @param acslPredCall
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateACSLPredicateCall(State state, int pid,
			ACSLPredicateCall acslPredCall)
			throws UnsatisfiablePathConditionException {
		List<SymbolicExpression> argumentValues = new LinkedList<>();
		Evaluation eval;
		int numArgs = acslPredCall.actualArguments().length;

		for (int i = 0; i < numArgs; i++) {
			eval = evaluate(state, pid, acslPredCall.actualArguments()[i]);
			assert state == eval.state : "ACSL predicate argument has side-effects.";
			argumentValues.add(eval.value);
		}

		CIVLFunctionType predType = acslPredCall.predicate().functionType();
		List<SymbolicType> paraTypes = new LinkedList<>();
		SymbolicFunctionType funcType;

		for (CIVLType type : predType.parameterTypes())
			paraTypes.add(type.getDynamicType(universe));
		funcType = universe.functionType(paraTypes, universe.booleanType());

		SymbolicExpression predCallValue = universe.symbolicConstant(
				universe.stringObject(acslPredCall.predicate().name().name()),
				funcType);

		return new Evaluation(state,
				universe.apply(predCallValue, argumentValues));
	}
}
