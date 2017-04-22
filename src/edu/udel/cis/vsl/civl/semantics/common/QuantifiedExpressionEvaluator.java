package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ExtendedQuantifiedExpressionNode.ExtendedQuantifier;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.ExtendedQuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.SubscriptExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.CartesianProductSolver;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * <p>
 * This class is a stateful evaluator for a single expression. All stateful
 * informations kept by this evaluator are only live within the evaluation of
 * the expression period. (Thus, for LibarayEvaluator or LibraryExecutors, their
 * primary evaluator should refer to a instance of this class during such a
 * stateful evaluation period).
 * </p>
 * 
 * <p>
 * This is a stateful evaluator for different kinds of quantified expressions:
 * <ul>
 * <li>Ordinary quantified expression: FORALL or EXISTS</li>
 * <li>Extended quantified expression (fold expression)</li>
 * <li>Lambda expression</li>
 * <li>Array lambda expression</li>
 * <li>Uniform expression</li>
 * <li>Big-O expression</li>
 * </ul>
 * <strong>No array-out-of bound error will be thrown by CIVL during the
 * evaluation of quantified expressions</strong>
 * </p>
 * 
 * The reason of why the above expressions need a stateful evaluation is: All of
 * this expressions are allowed to contain bounded or free variables and
 * restrictions. They can affect the evaluation state on their sub-expressions.
 * 
 * @author ziqing (Ready for review)
 *
 */
public class QuantifiedExpressionEvaluator
		extends
			ErrorSideEffectFreeEvaluator {

	/**
	 * A stack of map used to store bound variables during evaluation of
	 * (possibly nested) quantified expressions. LinkedList is used instead of
	 * Stack because of its more intuitive iteration order.
	 */
	protected LinkedList<Map<String, SymbolicConstant>> boundVariableStack = new LinkedList<>();

	/**
	 * This object represents a stack of restrictions specified by
	 * {@link ExtendedQuantifiedExpression}s. One extended quantified expression
	 * specifies a restriction on the free variable of its lambda expression via
	 * defining the bounds on it. For example
	 * <code> \sum(0, 10, \lambda i; i+1); </code> The restriction on free
	 * variable i is <code>0&lt= i &lt=10</code>.
	 */
	protected Stack<SymbolicExpression> extendedQuantifiedRestrictionsStack = new Stack<>();

	/**
	 * This object represents a stack of restrictions which is maintained during
	 * the recursive evaluation of {@link QuantifiedExpression}s. At any point
	 * of evaluating a bound variable, the restriction of the bound variable is
	 * the conjunction of all entries in this stack.
	 */
	protected Stack<BooleanExpression> quantifiedRestrictionsStack = new Stack<>();

	/**
	 * A Java function interface. An instance of this interface can be assigned
	 * by a Java method which has two {@link BooleanExpression}s as arguments
	 * and returns a {@link BooleanExpression}.
	 * 
	 * @author ziqing
	 *
	 */
	@FunctionalInterface
	private static interface LogicalOperation {
		BooleanExpression operation(BooleanExpression op0,
				BooleanExpression op1);
	}

	/**
	 * A Java function interface. An instance of this interface can be assigned
	 * by a Java method which has a {@link SymbolicConstant} argument and a
	 * {@link BooleanExpression} argument, returns a {@link BooleanExpression}.
	 * 
	 * @author ziqing
	 *
	 */
	@FunctionalInterface
	private static interface ApplyConstantOperation {
		BooleanExpression operation(SymbolicConstant boundVar,
				BooleanExpression pred);
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		if (expression.expressionKind() == ExpressionKind.BOUND_VARIABLE)
			return evaluateBoundVariable(state, pid,
					(BoundVariableExpression) expression);
		else
			return super.evaluate(state, pid, expression);
	}

	/**
	 * Constructor, parameters are similar to
	 * {@link CommonEvaluator#CommonEvaluator(ModelFactory, StateFactory, LibraryEvaluatorLoader, LibraryExecutorLoader, SymbolicUtility, SymbolicAnalyzer, MemoryUnitFactory, CIVLErrorLogger, CIVLConfiguration)}
	 */
	QuantifiedExpressionEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, MemoryUnitFactory memUnitFactory,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, loaderExec, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
	}

	/**
	 * <p>
	 * Evaluate an {@link ArrayLambdaExpression}
	 * </p>
	 * 
	 * @param state
	 *            The state where the evaluation happens
	 * @param pid
	 *            The PID of the process who invokes the evaluation
	 * @param arrayLambda
	 *            The expression that will be evaluated
	 * @return The evaluation result
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	protected Evaluation evaluateArrayLambda(State state, int pid,
			ArrayLambdaExpression arrayLambda)
			throws UnsatisfiablePathConditionException {
		List<Pair<List<Variable>, Expression>> boundVariableList = arrayLambda
				.boundVariableList();
		CIVLCompleteArrayType exprType = arrayLambda.getExpressionType();
		NumericSymbolicConstant[] boundVariables;
		TypeEvaluation typeEval = getDynamicType(state, pid, exprType,
				arrayLambda.getSource(), false);
		SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) typeEval.type;
		Evaluation eval;
		int numBoundVars = 0;

		boundVariables = new NumericSymbolicConstant[exprType.dimension()];
		state = typeEval.state;
		boundVariableStack.push(new HashMap<>());
		for (Pair<List<Variable>, Expression> boundVariableSubList : boundVariableList) {
			if (boundVariableSubList.right != null)
				throw new CIVLUnimplementedFeatureException(
						"declaring bound variables within a specific domain in array lambdas",
						arrayLambda.getSource());
			for (Variable variable : boundVariableSubList.left) {
				NumericSymbolicConstant boundVariable;

				assert variable.type().isIntegerType();
				boundVariable = (NumericSymbolicConstant) universe
						.symbolicConstant(variable.name().stringObject(),
								variable.type().getDynamicType(universe));
				boundVariables[numBoundVars++] = boundVariable;
				boundVariableStack.peek().put(boundVariable.name().getString(),
						boundVariable);
			}
		}
		assert exprType.dimension() == numBoundVars;
		if (arrayLambda.restriction() != null) {
			eval = evaluate(state, pid, arrayLambda.restriction());
			if (!eval.value.isTrue())
				throw new CIVLUnimplementedFeatureException(
						"non-trivial restriction expression in array lambdas",
						arrayLambda.getSource());
		}
		eval = new Evaluation(state, arrayLambda(state, pid, boundVariables, 0,
				arrayType, arrayLambda.expression()));
		boundVariableStack.pop();
		return eval;
	}

	/**
	 * <p>
	 * Creates an array lambda symbolic expression recursively (If it is a
	 * multi-dimensional array, the created one will be a nested array lambda
	 * expression).
	 * 
	 * </p>
	 * 
	 * @param state
	 *            The state where the array lambda expression body will evaluate
	 * @param pid
	 *            The PID of the process who invokes the creation of array
	 *            lambda expressions.
	 * @param boundVariables
	 *            An array of bound variables specified by the array lambda
	 *            expression
	 * @param boundIndex
	 *            The index of the bound variable in the array which belongs to
	 *            the current sub-array-lambda expression.
	 * @param arrayType
	 *            The symbolic type of a array lambda expression, which must be
	 *            a complete array type
	 * @param body
	 *            The lambda expression body of the array lambda
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected SymbolicExpression arrayLambda(State state, int pid,
			NumericSymbolicConstant[] boundVariables, int boundIndex,
			SymbolicCompleteArrayType arrayType, Expression body)
			throws UnsatisfiablePathConditionException {
		// TODO: The logic of this method is so simple that there is no need to
		// make it a recursive method, someone can try to use a loop instead.
		// Recursive calls is a little bit more expensive than using loop.
		NumericSymbolicConstant index = boundVariables[boundIndex];
		SymbolicExpression eleValue;
		SymbolicExpression arrayEleFunction;
		Evaluation eval;
		State tmpState; // temporary state only for evaluation

		tmpState = stateFactory.addToPathcondition(state, pid,
				universe.and(universe.lessThanEquals(zero, index),
						universe.lessThan(index, arrayType.extent())));
		if (boundIndex == boundVariables.length - 1) {
			eval = evaluate(tmpState, pid, body);
			eleValue = eval.value;
		} else
			eleValue = arrayLambda(tmpState, pid, boundVariables,
					boundIndex + 1,
					(SymbolicCompleteArrayType) arrayType.elementType(), body);
		arrayEleFunction = universe.lambda(index, eleValue);
		return universe.arrayLambda(arrayType, arrayEleFunction);
	}

	/**
	 * Evaluates a bound variable expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process who invokes the evaluation.
	 * @param expression
	 *            The bound variable expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bound variable expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation evaluateBoundVariable(State state, int pid,
			BoundVariableExpression expression) {
		SymbolicConstant value = null;
		String name = expression.name().name();

		for (Map<String, SymbolicConstant> boundVariableSet : boundVariableStack) {
			value = boundVariableSet.get(name);
			if (value != null)
				break;
		}
		if (value == null)
			throw new CIVLInternalException(
					"unreachable: unknown bound variable",
					expression.getSource());
		if (value.isNumeric()) {
			Reasoner reasoner = universe
					.reasoner(state.getPathCondition(universe));
			Number number = reasoner.extractNumber((NumericExpression) value);

			if (number != null)
				return new Evaluation(state, universe.number(number));
		}
		return new Evaluation(state, value);
	}

	@Override
	protected Evaluation evaluateQuantifiedExpression(State state, int pid,
			QuantifiedExpression expression)
			throws UnsatisfiablePathConditionException {
		List<Pair<List<Variable>, Expression>> boundVariableList = expression
				.boundVariableList();
		BooleanExpression restriction = universe.trueExpression();
		Evaluation eval;
		int index = 0;
		int numBoundVars = expression.numBoundVariables();
		SymbolicConstant[] boundVariables = new SymbolicConstant[numBoundVars];

		this.boundVariableStack.push(new HashMap<>());
		for (Pair<List<Variable>, Expression> boundVariableSubList : boundVariableList) {
			List<Variable> boundVariableDecls = boundVariableSubList.left;
			Expression domain = boundVariableSubList.right;
			SymbolicConstant boundValue;

			if (domain != null && boundVariableDecls.size() > 1)
				throw new CIVLUnimplementedFeatureException(
						"declaring bound variables within a specific domain in quantified expressions",
						expression.getSource());
			if (domain != null) {
				// range
				Variable boundVar = boundVariableDecls.get(0);
				SymbolicExpression range;
				NumericExpression lower, upper;

				assert boundVariableDecls.size() == 1;
				boundValue = universe.symbolicConstant(
						boundVar.name().stringObject(),
						boundVar.type().getDynamicType(universe));
				eval = this.evaluate(state, pid, domain);
				// TODO assert domain has dimension one
				boundVariables[index++] = boundValue;
				this.boundVariableStack.peek()
						.put(boundValue.name().getString(), boundValue);
				state = eval.state;
				range = eval.value;
				lower = this.symbolicUtil.getLowOfRegularRange(range);
				upper = this.symbolicUtil.getHighOfRegularRange(range);
				restriction = universe.and(restriction, universe.and(
						this.universe.lessThanEquals(lower,
								(NumericExpression) boundValue),
						this.universe.lessThanEquals(
								(NumericExpression) boundValue, upper)));
			} else {
				for (Variable boundVar : boundVariableDecls) {
					boundValue = universe.symbolicConstant(
							boundVar.name().stringObject(),
							boundVar.type().getDynamicType(universe));
					boundVariables[index++] = boundValue;
					this.boundVariableStack.peek()
							.put(boundValue.name().getString(), boundValue);
				}
			}
		}
		eval = this.evaluate(state, pid, expression.restriction());
		state = eval.state;
		restriction = universe.and(restriction, (BooleanExpression) eval.value);
		quantifiedRestrictionsStack.push(restriction);

		Evaluation result;
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));

		if (reasoner.valid(universe.not(restriction))
				.getResultType() == ResultType.YES) {
			// invalid range restriction
			switch (expression.quantifier()) {
				case EXISTS :
					result = new Evaluation(state, universe.falseExpression());
					break;
				default :// FORALL UNIFORM
					result = new Evaluation(state, universe.trueExpression());
			}
		} else {
			List<BooleanExpression> simplifiedClauses;
			BooleanExpression predicate;
			// function references, see how do they be assigned with methods
			// from universe in the switch block below:
			LogicalOperation clauseCombiner, restirctionCombiner;
			ApplyConstantOperation quantifiedExpression;

			// This is the simplification procedure explained above:
			simplifiedClauses = evaluateBoundedExpression(state, pid,
					expression.expression(), boundVariables);
			switch (expression.quantifier()) {
				case EXISTS :
					clauseCombiner = universe::or;
					restirctionCombiner = universe::and;
					quantifiedExpression = universe::exists;
					predicate = universe.falseExpression();
					break;
				case FORALL :
					clauseCombiner = universe::and;
					restirctionCombiner = universe::implies;
					quantifiedExpression = universe::forall;
					predicate = universe.trueExpression();
					break;
				default :
					throw new CIVLInternalException(
							"Unknown quantifier: " + expression.quantifier(),
							expression.getSource());
			}
			for (BooleanExpression clause : simplifiedClauses)
				predicate = clauseCombiner.operation(predicate, clause);
			predicate = restirctionCombiner.operation(restriction, predicate);
			for (SymbolicConstant complexBoundVar : boundVariables)
				predicate = quantifiedExpression.operation(complexBoundVar,
						predicate);
			result = new Evaluation(state, predicate);
		}
		boundVariableStack.pop();
		quantifiedRestrictionsStack.pop();
		return result;
	}

	/**
	 * <p>
	 * Evaluates a quantified predicate with elaboration of bound variables. For
	 * a tuple v of bound variables, there will be a set of tuples T of values
	 * as the elaboration of v. This method returns a set of evaluations of the
	 * predicate, each of which associates to a tuple t in T.
	 * </p>
	 * 
	 * 
	 * @param state
	 *            The current state when calling this method.
	 * @param pid
	 *            The PID of the calling process
	 * @param predicate
	 *            The boolean type {@link Expression} which will be evaluated
	 *            and may be simplified.
	 * @param boundVariables
	 *            Input and Output argument. A tuple of bound variables. For
	 *            each bound variable v in the tuple, if v is successfully
	 *            elaborated, it will be set to null.
	 * @return A list of evaluations of the given predicate.
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<BooleanExpression> evaluateBoundedExpression(State state,
			int pid, Expression predicate, SymbolicConstant[] boundVariables)
			throws UnsatisfiablePathConditionException {
		Reasoner reasoner;
		BitSet simplified = new BitSet();
		List<List<SymbolicExpression>> intervals = new LinkedList<>();
		BooleanExpression restriction = universe.trueExpression();

		for (BooleanExpression restrict : quantifiedRestrictionsStack)
			restriction = universe.and(restrict, restriction);
		reasoner = universe.reasoner(restriction);
		for (int i = 0; i < boundVariables.length; i++) {
			if (!boundVariables[i].isNumeric())
				continue;

			// Interval interval = reasoner.intervalApproximation(
			// (NumericExpression) boundVariables[i]);
			Interval interval = reasoner.intervalApproximation(
					(NumericSymbolicConstant) boundVariables[i]);

			// We can only simplify symbolic constants which have non-null
			// integeral intervals. And all intervals must have finite numbers
			// as bounds:
			if (interval != null && interval.isIntegral()
					&& !interval.lower().isInfinite()
					&& !interval.upper().isInfinite()) {
				Number high = interval.upper();
				Number low = interval.lower();
				List<SymbolicExpression> vector = new LinkedList<>();

				while (universe.numberFactory().compare(high, low) >= 0) {
					vector.add(universe.number(low));
					low = universe.numberFactory().increment(low);
				}
				intervals.add(vector);
				simplified.set(i);
			} else
				intervals.add(Arrays.asList(boundVariables[i]));
		}

		CartesianProductSolver<SymbolicExpression> solver = new CartesianProductSolver<>(
				intervals);
		List<BooleanExpression> clauses = new LinkedList<>();

		for (List<SymbolicExpression> vector : solver) {
			Reasoner contextReasoner;
			BooleanExpression restrictionAndVector = restriction;
			BooleanExpression pc = state.getPathCondition(universe);
			State newState;
			Evaluation eval;
			int varIdx = 0;

			for (SymbolicExpression value : vector)
				restrictionAndVector = universe.and(restrictionAndVector,
						universe.equals(boundVariables[varIdx++], value));
			// If restriction (context) is unsatisfiable, skip:
			contextReasoner = universe.reasoner(universe.trueExpression());
			if (contextReasoner.isValid(
					universe.not(universe.and(pc, restrictionAndVector))))
				continue;
			else {
				newState = stateFactory.addToPathcondition(state, pid,
						restrictionAndVector);
				eval = evaluate(newState, pid, predicate);
				clauses.add((BooleanExpression) eval.value);
			}
		}
		// Eliminate simplified bound variables:
		// for (int varId = simplified.nextSetBit(
		// 0); varId >= 0; varId = simplified.nextSetBit(varId + 1))
		// boundVariables[varId] = null;
		return clauses;
	}

	/**
	 * Evaluate an {@link ExtendedQuantifiedExpression}
	 * 
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	protected Evaluation evaluateExtendedQuantifiedExpression(State state,
			int pid, ExtendedQuantifiedExpression extQuant)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		Expression function = extQuant.function();
		NumericExpression low, high;
		ExtendedQuantifier quant = extQuant.extendedQuantifier();
		CIVLSource source = extQuant.getSource();

		eval = evaluate(state, pid, extQuant.lower());
		state = eval.state;
		low = (NumericExpression) eval.value;
		eval = evaluate(state, pid, extQuant.higher());
		high = (NumericExpression) eval.value;
		state = eval.state;

		NumericSymbolicConstant idx = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		BooleanExpression restriction = universe.lessThanEquals(low, idx);
		Number lowNum, highNum;
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		TypeEvaluation typeEval = this.getDynamicType(state, pid,
				extQuant.getExpressionType(), source, false);

		restriction = universe.and(restriction,
				universe.lessThanEquals(idx, high));
		// Push a lambda function into the stack. During the evaluation of the
		// extended-quantified expression, applying the top stack entry to a
		// free variable in a lambda expression will return a boolean-value
		// restriction for the free variable:
		extendedQuantifiedRestrictionsStack
				.push(universe.lambda(idx, restriction));
		lowNum = reasoner.extractNumber(low);
		highNum = reasoner.extractNumber(high);
		eval = evaluate(typeEval.state, pid, function);
		// Using different helper methods for concrete and non-concrete cases:
		if (lowNum != null && highNum != null) {
			int lowInt, highInt;

			lowInt = ((IntegerNumber) lowNum).intValue();
			highInt = ((IntegerNumber) highNum).intValue();
			eval.value = computeConcreteFoldExpression(lowInt, highInt,
					eval.value, quant, typeEval.type, source);
		} else
			eval = computeNonconcreteFoldExpression(eval.state, pid, reasoner,
					low, high, eval.value, quant, source);
		extendedQuantifiedRestrictionsStack.pop();
		return eval;
	}

	/**
	 * 
	 * <p>
	 * Evaluate {@link ExtendedQuantifiedExpression} e(i,j,f):
	 * <code>f(i) op f(i+1) op ... op f(j)</code> where i &lt= j and op stands
	 * for an {@link ExtendedQuantifier}.
	 * 
	 * This method requires both i and j have non-concrete values.
	 * 
	 * If j > i can be proved, an induction step will be added to the path
	 * condition: <code>e(i,j,f) == e(i,j-1,f) + f(j)</code>
	 * </p>
	 * 
	 * @param state
	 *            The current state when this method is called
	 * @param reasoner
	 *            A reference to a {@link Reasoner}
	 * @param low
	 *            The lower bound of the parameter.
	 * @param high
	 *            The higher bound of the parameter.
	 * @param lambda
	 *            The lambda expression which maps the parameter to an
	 *            expression
	 * @param quant
	 *            The {@link ExtendedQuantifier} which is a kind of a binary
	 *            operator
	 * @param source
	 *            The {@link CIVLSource} related to this method call
	 * @return
	 */
	private Evaluation computeNonconcreteFoldExpression(State state, int pid,
			Reasoner reasoner, NumericExpression low, NumericExpression high,
			SymbolicExpression lambda, ExtendedQuantifier quant,
			CIVLSource source) {
		// The prevResult is kind like the laste one step in induction, for
		// example summation(0, n) == n + summation(0, n-1):
		NumericExpression result, inductive = null;

		if (reasoner.isValid(universe.lessThan(high, low))) {
			result = ((SymbolicFunctionType) lambda.type()).outputType()
					.isInteger() ? universe.zeroInt() : universe.zeroReal();
			return new Evaluation(state, result);
		}
		switch (quant) {
			case SUM :
				NumericExpression highMinusOne = universe.subtract(high, one);
				BooleanExpression highMinusOneLtLow = universe
						.lessThan(highMinusOne, low);

				result = (NumericExpression) universe.sigma(low, high, lambda);
				if (!reasoner.isValid(highMinusOneLtLow)) {
					inductive = (NumericExpression) universe.sigma(low,
							highMinusOne, lambda);
					inductive = universe.add(inductive,
							(NumericExpression) universe.apply(lambda,
									Arrays.asList(high)));
				}
				break;
			default :
				throw new CIVLUnimplementedFeatureException(
						"evaluating non-concrete extended quantification "
								+ quant,
						source);
		}
		return new Evaluation(state, result);
	}

	/**
	 * <p>
	 * Evaluate {@link ExtendedQuantifiedExpression} :
	 * <code>f(i) op f(i+1) op ... op f(j)</code> where i &lt= j and op stands
	 * for an {@link ExtendedQuantifier}.
	 * 
	 * This method requires both i and j have concrete values.
	 * </p>
	 * 
	 * @param low
	 *            The lower bound of the parameter.
	 * @param high
	 *            The higher bound of the parameter.
	 * @param lambda
	 *            The lambda expression which maps the parameter to an
	 *            expression
	 * @param quant
	 *            The {@link ExtendedQuantifier} which is a kind of a binary
	 *            operator
	 * @param expressionType
	 *            The expression type of this
	 *            {@link ExtendedQuantifiedExpression}.
	 * @param source
	 *            The {@link CIVLSource} related to this method call
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private NumericExpression computeConcreteFoldExpression(int low, int high,
			SymbolicExpression lambda, ExtendedQuantifier quant,
			SymbolicType expressionType, CIVLSource source) {
		if (high < low)
			return expressionType.isInteger()
					? universe.zeroInt()
					: universe.zeroReal();

		NumericExpression result = (NumericExpression) universe.apply(lambda,
				Arrays.asList(universe.integer(low)));

		for (int i = low + 1; i <= high; i++) {
			NumericExpression index = universe.integer(i);
			NumericExpression current;

			current = (NumericExpression) universe.apply(lambda,
					Arrays.asList(index));
			switch (quant) {
				case SUM :
					result = universe.add(result, current);
					break;
				case PROD :
					result = universe.multiply(result, current);
					break;
				default :
					throw new CIVLUnimplementedFeatureException(
							"evaluating concrete extended quantification "
									+ quant,
							source);
			}
		}
		return result;
	}

	@Override
	protected Evaluation evaluateLambda(State state, int pid,
			LambdaExpression lambda)
			throws UnsatisfiablePathConditionException {
		Variable freeVariable = lambda.freeVariable();
		Evaluation eval = null;
		TypeEvaluation typeEval;
		SymbolicType varType;
		NumericSymbolicConstant freeVariableValue;

		typeEval = getDynamicType(state, pid, freeVariable.type(),
				freeVariable.getSource(), false);
		state = typeEval.state;
		varType = typeEval.type;
		boundVariableStack.push(new HashMap<>());
		freeVariableValue = (NumericSymbolicConstant) universe
				.symbolicConstant(freeVariable.name().stringObject(), varType);
		boundVariableStack.peek().put(freeVariableValue.name().getString(),
				freeVariableValue);

		State oldState = state;

		if (!extendedQuantifiedRestrictionsStack.isEmpty()) {
			SymbolicExpression restrictFunction = extendedQuantifiedRestrictionsStack
					.peek();
			BooleanExpression restriction;

			restriction = (BooleanExpression) universe.apply(restrictFunction,
					Arrays.asList(freeVariableValue));
			assert restriction.type()
					.typeKind() == SymbolicType.SymbolicTypeKind.BOOLEAN;
			state = stateFactory.addToPathcondition(state, pid, restriction);
		}
		eval = evaluate(state, pid, lambda.lambdaFunction());
		eval.state = oldState;
		eval.value = universe.lambda(freeVariableValue, eval.value);
		boundVariableStack.pop();
		return eval;
	}

	// No bound checking during the evaluation of lambda expression
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
}
