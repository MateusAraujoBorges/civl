package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.expression.ArrayLambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BoundVariableExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LambdaExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.OriginalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ValueAtExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLFunctionType;
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

public class QuantifiedExpressionEvaluator extends CommonEvaluator {

	/**
	 * LinkedList used to store a stack of bound variables during evaluation of
	 * (possibly nested) quantified expressions. LinkedList is used instead of
	 * Stack because of its more intuitive iteration order.
	 */
	protected Stack<Set<SymbolicConstant>> boundVariableStack = new Stack<>();

	private State originalState = null;

	private int originalPid = -1;

	private int valueAtOrRemoteCount = 0;

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		if (expression.expressionKind() == ExpressionKind.BOUND_VARIABLE) {
			return evaluateBoundVariable(state, pid,
					(BoundVariableExpression) expression);
		} else {
			return super.evaluate(state, pid, expression);
		}
	}

	public QuantifiedExpressionEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, MemoryUnitFactory memUnitFactory,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, loaderExec, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
		// TODO Auto-generated constructor stub
	}

	/**
	 * in general, there is an assertion that must be checked <br>
	 * assert(0<=i<n -> RESTRICT);<br>
	 * assert ($forall (int i: 0.. n-1) RESTRICT);
	 * 
	 * @param state
	 * @param pid
	 * @param arrayLambda
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	protected Evaluation evaluateArrayLambda(State state, int pid,
			ArrayLambdaExpression arrayLambda)
					throws UnsatisfiablePathConditionException {
		List<Pair<List<Variable>, Expression>> boundVariableList = arrayLambda
				.boundVariableList();
		BooleanExpression restriction = universe.trueExpression();
		Evaluation eval = null;
		int dim = ((CIVLArrayType) arrayLambda.getExpressionType()).dimension(),
				numBoundVars = 0;
		NumericSymbolicConstant[] boundVariables = new NumericSymbolicConstant[dim];
		TypeEvaluation typeEval = this.getDynamicType(state, pid,
				(CIVLArrayType) arrayLambda.getExpressionType(),
				arrayLambda.getSource(), false);
		SymbolicCompleteArrayType arrayType = (SymbolicCompleteArrayType) typeEval.type;

		state = typeEval.state;
		this.boundVariableStack.push(new HashSet<SymbolicConstant>());
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
				this.boundVariableStack.peek().add(boundVariable);
			}
		}
		assert dim == numBoundVars;
		if (arrayLambda.restriction() != null) {
			eval = this.evaluate(state, pid, arrayLambda.restriction());
			restriction = universe.and(restriction,
					(BooleanExpression) eval.value);
			state = eval.state;
		}
		if (restriction.isFalse())
			return new Evaluation(state, universe.nullExpression());
		if (!restriction.isTrue())
			throw new CIVLUnimplementedFeatureException(
					"non-trivial restriction expression in array lambdas",
					arrayLambda.getSource());
		eval = new Evaluation(state, this.arrayLambda(state, pid,
				boundVariables, 0, arrayType, arrayLambda.expression()));
		this.boundVariableStack.pop();
		return eval;
	}

	/**
	 * Evaluates a bound variable expression.
	 * 
	 * @param state
	 *            The state where the evaluation happens.
	 * @param pid
	 *            The PID of the process that triggers the evaluation.
	 * @param expression
	 *            The bound variable expression to be evaluated.
	 * @return A possibly new state resulted from side effects during the
	 *         evaluation and the value of the bound variable expression.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation evaluateBoundVariable(State state, int pid,
			BoundVariableExpression expression) {
		SymbolicConstant value = null;

		for (Set<SymbolicConstant> boundVariableSet : this.boundVariableStack) {
			for (SymbolicConstant boundVariable : boundVariableSet) {
				if (boundVariable.name().toString()
						.equals(expression.name().name()))
					value = boundVariable;
			}
		}
		if (value == null)
			throw new CIVLInternalException(
					"unreachable: unknown bound variable",
					expression.getSource());
		return new Evaluation(state, value);
	}

	@Override
	protected Evaluation evaluateLambda(State state, int pid,
			LambdaExpression arrayLambda)
					throws UnsatisfiablePathConditionException {
		List<Pair<List<Variable>, Expression>> boundVariableList = arrayLambda
				.boundVariableList();
		Evaluation eval = null;
		int numBoundVars = 0;
		TypeEvaluation typeEval = this.getDynamicType(state, pid,
				(CIVLFunctionType) arrayLambda.getExpressionType(),
				arrayLambda.getSource(), false);
		SymbolicFunctionType arrayType = (SymbolicFunctionType) typeEval.type;
		int numInputs = arrayType.inputTypes().numTypes();
		NumericSymbolicConstant[] boundVariables = new NumericSymbolicConstant[numInputs];
		SymbolicExpression restriction;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		state = typeEval.state;
		this.boundVariableStack.push(new HashSet<SymbolicConstant>());
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
				this.boundVariableStack.peek().add(boundVariable);
			}
		}
		assert numInputs == numBoundVars;
		eval = evaluate(state, pid, arrayLambda.restriction());
		restriction = eval.value;
		if (!reasoner.isValid((BooleanExpression) restriction)) {
			throw new CIVLUnimplementedFeatureException(
					"non-trivial restriction used in lambda expression",
					arrayLambda.getSource());
		}
		// if (restriction.isFalse())
		// return new Evaluation(state, universe.nullExpression());
		// if (!restriction.isTrue())
		// throw new CIVLUnimplementedFeatureException(
		// "non-trivial restriction expression in array lambdas",
		// arrayLambda.getSource());
		eval = new Evaluation(state, this.lambda(state, pid, boundVariables, 0,
				arrayType, arrayLambda.expression()));
		this.boundVariableStack.pop();
		return eval;
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

		this.boundVariableStack.push(new HashSet<SymbolicConstant>());
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
				this.boundVariableStack.peek().add(boundValue);
				state = eval.state;
				range = eval.value;
				lower = this.symbolicUtil.getLowOfRegularRange(range);
				upper = this.symbolicUtil.getHighOfRegularRange(range);
				restriction = universe.and(restriction,
						universe.and(
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
					this.boundVariableStack.peek().add(boundValue);
				}
			}
		}
		eval = this.evaluate(state, pid, expression.restriction());
		state = eval.state;
		restriction = universe.and(restriction, (BooleanExpression) eval.value);

		Interval interval = null;
		NumericExpression lower = null, upper = null;
		ResultType isRestrictionInValid;
		Evaluation result;
		State stateWithRestriction;
		Evaluation quantifiedExpression;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		BooleanExpression simplifiedExpression;

		isRestrictionInValid = reasoner.valid(universe.not(restriction))
				.getResultType();
		if (isRestrictionInValid == ResultType.YES) {
			// invalid range restriction
			switch (expression.quantifier()) {
				case EXISTS :
					result = new Evaluation(state, universe.falseExpression());
					break;
				default :// FORALL UNIFORM
					result = new Evaluation(state, universe.trueExpression());
			}
		} else {
			BooleanExpression quantifiedExpressionNew = null;
			BooleanExpression context = universe.and(restriction,
					state.getPathCondition());

			stateWithRestriction = state.setPathCondition(context);
			quantifiedExpression = evaluate(stateWithRestriction, pid,
					expression.expression());
			context = quantifiedExpression.state.getPathCondition();
			reasoner = universe.reasoner(context);
			simplifiedExpression = (BooleanExpression) reasoner
					.simplify(quantifiedExpression.value);
			quantifiedExpressionNew = simplifiedExpression;
			for (int i = numBoundVars - 1; i >= 0; i--) {
				SymbolicConstant boundVar = boundVariables[i];

				interval = reasoner.assumptionAsInterval(boundVar);
				if (interval != null) {
					lower = universe.number(interval.lower());
					upper = universe.add(universe.number(interval.upper()),
							this.one);
				}
				switch (expression.quantifier()) {
					case EXISTS :
						if (interval != null)
							quantifiedExpressionNew = universe.existsInt(
									(NumericSymbolicConstant) boundVar, lower,
									upper,
									(BooleanExpression) quantifiedExpressionNew);
						else
							quantifiedExpressionNew = universe.exists(boundVar,
									universe.and(restriction,
											quantifiedExpressionNew));
						break;
					case FORALL :
						if (interval != null)
							quantifiedExpressionNew = universe.forallInt(
									(NumericSymbolicConstant) boundVar, lower,
									upper,
									(BooleanExpression) quantifiedExpressionNew);
						else
							quantifiedExpressionNew = universe.forall(boundVar,
									universe.implies(restriction,
											quantifiedExpressionNew));
						break;
					case UNIFORM :
						if (interval != null)
							quantifiedExpressionNew = universe.forallInt(
									(NumericSymbolicConstant) boundVar, lower,
									upper,
									(BooleanExpression) quantifiedExpressionNew);
						else
							quantifiedExpressionNew = universe.forall(boundVar,
									universe.implies(restriction,
											quantifiedExpressionNew));
						break;
					default :
						throw new CIVLException("Unknown quantifier ",
								expression.getSource());
				}
			}
			result = new Evaluation(state, quantifiedExpressionNew);
		}
		boundVariableStack.pop();
		return result;
	}

	private BooleanExpression getPredicateOnBoundVariables(State state) {
		BooleanExpression pc = state.getPathCondition();
		BooleanExpression context = universe.trueExpression();
		BooleanExpression[] clauses = symbolicUtil.getConjunctiveClauses(pc);

		if (!this.boundVariableStack.isEmpty()) {
			for (Set<SymbolicConstant> varSet : boundVariableStack) {
				for (SymbolicConstant var : varSet) {
					for (BooleanExpression clause : clauses) {
						if (containsSymbolicConstant(clause, var))
							context = universe.and(context, clause);
					}
				}
			}
		}
		return context;
	}

	private void enterValueAtOrRemote(State state, int pid) {
		if (this.valueAtOrRemoteCount == 0) {
			this.originalState = state;
			this.originalPid = pid;
		}
		valueAtOrRemoteCount++;
	}

	private void exitValueAtOrRemote() {
		valueAtOrRemoteCount--;
		if (this.valueAtOrRemoteCount == 0) {
			this.originalState = null;
			this.originalPid = -1;
		}
	}

	/**
	 * Evaluates a 'remote access' expression. A 'remote access' expression
	 * consists of an expression and a process ID, it means evaluteing the
	 * expression on the process with the given ID.
	 * 
	 * @param state
	 *            The current program state when the evaluation happens
	 * @param pid
	 *            The PID of the current on the control process
	 * @param expression
	 *            The {@link BinaryExpression} with a REMOTE operator.
	 * @return The evaluation of the binary expression
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	protected Evaluation evaluateRemoteOperation(State state, int pid,
			BinaryExpression expression)
					throws UnsatisfiablePathConditionException {
		Expression procExpr = expression.left();
		Expression exprExpr = expression.right();
		Evaluation eval = evaluate(state, pid, procExpr);
		NumericExpression proc;
		Reasoner reasoner;

		state = eval.state;
		proc = (NumericExpression) eval.value;
		reasoner = universe.reasoner(state.getPathCondition());

		Number procNum = reasoner.extractNumber(proc);
		int procNumVal;

		if (procNum == null)
			throw new CIVLInternalException(
					"Remote expression on a non-concrete process : "
							+ symbolicAnalyzer.expressionEvaluation(state, pid,
									procExpr, true).right,
					procExpr.getSource());
		procNumVal = ((IntegerNumber) procNum).intValue();
		if (state.numProcs() <= procNumVal) {
			String process = state.getProcessState(pid).name();
			StringBuffer message = new StringBuffer();
			String procExpression = "Process expression :";
			char padding[] = new char[procExpression.length()];

			Arrays.fill(padding, ' ');
			message.append(
					"Remote expression refers to a process p" + procNumVal
							+ " that not exists in the corresponding state:\n");
			message.append(procExpression
					+ symbolicAnalyzer.expressionEvaluation(state, pid,
							procExpr, false).right
					+ "\n" + String.valueOf(padding) + " => "
					+ symbolicAnalyzer.expressionEvaluation(state, pid,
							procExpr, true).right
					+ "\n" + String.valueOf(padding) + " =>");
			message.append(symbolicAnalyzer.symbolicExpressionToString(
					procExpr.getSource(), state, procExpr.getExpressionType(),
					proc) + "\n");
			errorLogger.logSimpleError(procExpr.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					message.toString());
		}
		enterValueAtOrRemote(state, pid);
		eval = evaluate(state, procNumVal, exprExpr);
		exitValueAtOrRemote();
		// shall not affect the remoted process state and global state:
		eval.state = state;
		return eval;
	}

	@Override
	public Evaluation evaluateOriginalExpression(State state, int pid,
			OriginalExpression original)
					throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(this.originalState, this.originalPid,
				original.expression());

		this.originalState = eval.state;
		eval.state = state;
		return eval;
	}

	@Override
	public Evaluation evaluateValueAtExpression(State state, int pid,
			ValueAtExpression valueAt)
					throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluate(state, pid, valueAt.state());
		SymbolicExpression stateRef;
		NumericExpression place;
		CIVLSource source = valueAt.getSource();
		String process = state.getProcessState(pid).name();
		State colState;
		int newPID;

		state = eval.state;
		stateRef = eval.value;
		eval = evaluate(state, pid, valueAt.pid());
		place = (NumericExpression) eval.value;
		state = eval.state;
		newPID = symbolicUtil.extractInt(source, place);
		if (newPID < 0)
			newPID = pid;
		colState = this.stateFactory.getStateByReference(
				modelFactory.getStateRef(source, stateRef));
		if (newPID >= colState.numProcs()) {
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"invalid process ID");
		}
		colState = colState
				.setPathCondition(universe.and(colState.getPathCondition(),
						getPredicateOnBoundVariables(state)));
		enterValueAtOrRemote(state, pid);
		eval = this.evaluate(colState, newPID, valueAt.expression());
		exitValueAtOrRemote();
		eval.state = state;
		return eval;
	}

}
