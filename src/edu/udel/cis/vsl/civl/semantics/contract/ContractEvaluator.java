package edu.udel.cis.vsl.civl.semantics.contract;

import java.util.HashSet;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiEvaluator;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression.Quantifier;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression.UNARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.common.CommonEvaluator;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;

/**
 * This class extends {@link CommonEvaluator} with contracts evaluating
 * semantics.
 * <p>
 * This is a summary of the extension or over-written for contracts system:
 * General section:
 * <ol>
 * <li><b>\valid(pointer set):</b> denotes a set of pointers P are valid, i.e.
 * for all pointer p in P, p is dereferable. Currently there are some
 * <b>limitations</b> on how to write valid expressions:
 * <ul>
 * <li>The pointer set P can only be written in two forms: a single pointer
 * expression which represents a singleton set; a pointer plus a range which
 * represents a set of pointers <code>{p + i | i in range}</code>.</li>
 * <li>For the range (low .. high), low must be zero, high must be bounded, step
 * can only be one.</li>
 * </ul>
 * </li>
 * <li><b>\remote(variable, process):</b> expresses a remote expression. A
 * remote expression evaluates to the evaluation of the variable on the process.
 * NOTE there are two restrictions on use of remote expressions:
 * <ul>
 * <li>There is no guarantee for the evaluation of a remote expression if the
 * control point where the evaluation happens of the remote process is
 * non-deterministic.</li>
 * <li>All free variables V appear in the process expression of a remote
 * expression must be deterministic.</li>
 * </ul>
 * These two restrictions are suppose to avoid the difficulty of building the
 * start state of a verifying function and more importantly non-sense remote
 * expressions.</li>
 * <li><b>Dereference:</b> The dereferencing operation must be able to recognize
 * whether undereferable pointers are concrete and not guaranteed to be valid.</li>
 * </ol>
 * 
 * MPI section: Evaluation of MPI contract expressions and collective evaluation
 * see {@link LibmpiEvaluator}
 * </p>
 * 
 * @author ziqingluo
 *
 */
public class ContractEvaluator extends CommonEvaluator implements Evaluator {
	/**
	 * FINALIZED flag value for MPI system status variable
	 */
	public final NumericExpression FINALIZED;
	/**
	 * INITIALIZED flag value for MPI system status variable
	 */
	public final NumericExpression INITIALIZED;

	public ContractEvaluator(ModelFactory modelFactory,
			StateFactory stateFactory, LibraryEvaluatorLoader loader,
			LibraryExecutorLoader loaderExec, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		super(modelFactory, stateFactory, loader, loaderExec, symbolicUtil,
				symbolicAnalyzer, memUnitFactory, errorLogger, config);
		this.FINALIZED = universe.integer(2);
		this.INITIALIZED = universe.oneInt();
	}

	@Override
	public Evaluation evaluate(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException {
		ExpressionKind kind = expression.expressionKind();

		if (kind.equals(ExpressionKind.MPI_CONTRACT_EXPRESSION)) {
			String process = state.getProcessState(pid).name();

			return evaluateMPIContractExpression(state, pid, process,
					(MPIContractExpression) expression);
		} else
			return super.evaluate(state, pid, expression);
	}

	@Override
	protected Evaluation evaluateBinary(State state, int pid, String process,
			BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		BINARY_OPERATOR operator = expression.operator();

		if (operator.equals(BINARY_OPERATOR.REMOTE))
			return evaluateRemoteExpression(state, pid, process, expression);
		else
			return super.evaluateBinary(state, pid, process, expression);
	}

	/**
	 * <p>
	 * <b>Summary</b> Evaluate a {@link QuantifiedExpression}. If the
	 * restriction on the bounded variable can be translated to an concrete
	 * integral interval, then evaluation of the predicate happens on a set of
	 * concrete cases. Otherwise, call the super class method {@link
	 * super#evaluateQuantifiedExpression(State, int, QuantifiedExpression)}.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param expression
	 *            The quantified expression
	 * @return
	 */
	@Override
	protected Evaluation evaluateQuantifiedExpression(State state, int pid,
			QuantifiedExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression restriction = expression.restriction();
		Reasoner reasoner;
		NumericSymbolicConstant boundVariable;
		Interval boundInterval;
		Variable singleBoundVariable = expression.boundVariableList().get(0).left
				.get(0);

		this.boundVariableStack.push(new HashSet<SymbolicConstant>());
		// The restriction must a boolean expression, and the bound variable
		// must has a integral numeric type
		// if (restriction.getExpressionType().isBoolType())
		if (singleBoundVariable.type().isIntegerType()) {
			Evaluation restrictionVal;

			boundVariable = (NumericSymbolicConstant) universe
					.symbolicConstant(
							singleBoundVariable.name().stringObject(),
							singleBoundVariable.type().getDynamicType(universe));
			// push the bound variable for evaluation:
			// boundVariables.push(boundVariable);
			boundVariableStack.peek().add(boundVariable);
			restrictionVal = evaluate(state, pid, restriction);
			reasoner = universe
					.reasoner((BooleanExpression) restrictionVal.value);
			boundInterval = reasoner
					.intervalApproximation((NumericExpression) boundVariable);
			// If the bound interval exists, and the interval contains no
			// Infinities, the evaluation will happen by elaborating all
			// possible values:
			if (boundInterval != null) {
				Number lower, upper;

				lower = boundInterval.lower();
				upper = boundInterval.upper();
				if (lower instanceof IntegerNumber
						&& upper instanceof IntegerNumber) {
					int lowerInt = ((IntegerNumber) lower).intValue();
					int highInt = ((IntegerNumber) upper).intValue();

					if (expression.quantifier() == Quantifier.EXISTS)
						return evaluateElabortaedQuantifiedExpression(state,
								pid, boundVariable, expression.expression(),
								lowerInt, highInt, false);
					else if (expression.quantifier() == Quantifier.FORALL) {
						return evaluateElabortaedQuantifiedExpression(state,
								pid, boundVariable, expression.expression(),
								lowerInt, highInt, true);
					} else
						throw new CIVLUnimplementedFeatureException(
								"Reasoning quantified expressions with kinds that are not FORALL or EXISTS in function contracts");
				}
			}
			// pop the bound variable after evaluation:
			// boundVariables.pop();
			boundVariableStack.pop();
		}
		return super.evaluateQuantifiedExpression(state, pid, expression);
	}

	/**
	 * <p>
	 * <b> Pre-condition:</b>
	 * <ul>
	 * <li>higherBound >= lowerBound;</li>
	 * <li>The {@link QuantifiedExpression} only has one "bound variable";</li>
	 * <li>The "bound variable" has an integral type;</li>
	 * <li>The {@link QuantifiedExpression} is either a FORALL or EXISTS
	 * expression.</li>
	 * </ul>
	 * </p>
	 * <p>
	 * <b>Summary:</b> Evaluates a {@link QuantifiedExpression} by elaborating
	 * all possible values of the integral bounded variable.
	 * </p>
	 * <p>
	 * <b>Details:</b> The evaluation of the quantified predicate p happens on a
	 * set of evaluating states S, where all state s in S is not a state in the
	 * program state space. For each state s in S, it is obtained by updating
	 * the parameter "state" by adding an assumption a to the path condition of
	 * "state". Here assumption a is in set A which is a boolean expression set.
	 * Set A is a set of conditions on the bounded variable b:
	 * <code>{b == i | lowerBound \lte i && i \lte higherBound}</code>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param boundedVar
	 *            A symbolic constant representing the bounded variable.
	 * @param predExpression
	 *            The predication expression of the {@link QuantifiedExpression}
	 * @param lowerBound
	 *            Lower bound of the bounded variable
	 * @param higherBound
	 *            Higher bound of the bounded variable
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateElabortaedQuantifiedExpression(State state,
			int pid, NumericSymbolicConstant boundedVar,
			Expression predExpression, int lowerBound, int higherBound,
			boolean isForall) throws UnsatisfiablePathConditionException {
		State evalState;
		Evaluation eval;
		BooleanExpression result = null;
		boolean isFirst = true;

		// Elaborates all values for the bound variable:
		for (int i = lowerBound; i <= higherBound; i++) {
			BooleanExpression concretizeBoundVar = universe.equals(boundedVar,
					universe.integer(i));

			// Get an evaluating state by updating the path condition of the
			// parameter state:
			evalState = state.setPathCondition(universe.and(concretizeBoundVar,
					state.getPathCondition()));
			eval = evaluate(evalState, pid, predExpression);
			if (isFirst) {
				result = (BooleanExpression) eval.value;
				isFirst = false;
			} else {
				if (isForall)
					result = universe.and(result,
							(BooleanExpression) eval.value);
				else
					result = universe
							.or(result, (BooleanExpression) eval.value);
			}
			// Because the evaluating state s' is not a state in the execution
			// state space of the program, s' is only active in this method. So
			// if the validation of the result relies on reasoning on any
			// execution state s, it will go wrong because s doens't have
			// information about the bounded variable. Hence, this is the
			// solution here:
			//
			// Solution: If the result relies on reasoning with a state, the
			// result should be updated by substituting the bounded variable
			// with the elaborated concrete value:
			if (!(result.isTrue() || result.isFalse())) {
				UnaryOperator<SymbolicExpression> concretizeSubstituter = universe
						.simpleSubstituter(boundedVar, universe.integer(i));

				result = (BooleanExpression) concretizeSubstituter
						.apply(result);
			}
		}
		return new Evaluation(state, result);
	}

	/**
	 * <p>
	 * <b>Summary:</b> Evaluates a remote expression which has the form:
	 * <code>\remote(variable_identifier, process_expression) </code>
	 * </p>
	 * 
	 * <p>
	 * <b>Details:</b> The evaluation on a remote accessing expression follows
	 * the semantics:
	 * 
	 * A {@link BINARY_OPERATOR#REMOTE} operation takes two operands: left hand
	 * side operand represents a variable identifier v and the right hand side
	 * operand represents a process p.
	 *
	 * The whole expression evaluates to the evaluation of the variable v on
	 * process p. It requires that at the evaluation time, v must be visible at
	 * the location where the control of p is. Such a restriction indicates that
	 * remote expression can hardly be used at other lexical locations than
	 * contract expression. The use of remote expressions in contract see
	 * {@link ContractEvaluator}
	 * 
	 * A practical usage for remote expressions are expressing global properties
	 * for MPI programs. i.e. A property involves at least two MPI processes. An
	 * implicit requirements for the remote expression \remote(v, p) is v must
	 * be visible for both the current process and the process p at their
	 * current locations.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param expression
	 *            The remote expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateRemoteExpression(State state, int pid,
			String process, BinaryExpression expression)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression procVal, varVal = null;
		Expression procExpr = expression.right();
		VariableExpression varExpr = (VariableExpression) expression.left();
		Variable variable = null;
		Reasoner reasoner;
		Number remotePidNum;
		int remotePid;
		int dyscopeId;
		int vid = -1;

		eval = this.evaluate(state, pid, procExpr);
		state = eval.state;
		procVal = eval.value;
		// If the process expression is not a NumericExpression, report the
		// error:
		if (!(procVal instanceof NumericExpression)) {
			errorLogger.logSimpleError(procExpr.getSource(), state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"The right-hand side expression of a remote access "
							+ procExpr + " is not a numeric expression.");
			throw new UnsatisfiablePathConditionException();
		}
		reasoner = universe.reasoner(state.getPathCondition());
		// If no concrete value can be extracted from the symbolic "process"
		// value, report an error:
		remotePidNum = reasoner.extractNumber((NumericExpression) procVal);
		if (remotePidNum == null) {
			errorLogger.logSimpleError(procExpr.getSource(), state, process,
					symbolicAnalyzer.stateToString(state), ErrorKind.OTHER,
					"The right-hand side expression of a remote access "
							+ procExpr + " doesn not have a concrete value.");
			throw new UnsatisfiablePathConditionException();
		}
		remotePid = ((IntegerNumber) remotePidNum).intValue();
		dyscopeId = state.getProcessState(remotePid).getDyscopeId();
		variable = varExpr.variable();
		// looking for the first visible variable from the current location of
		// process procVal that has the same name as the remote variable:
		while (dyscopeId != -1) {
			Scope scope1 = state.getDyscope(dyscopeId).lexicalScope();

			if (scope1.containsVariable(variable.name().name())) {
				vid = scope1.variable(variable.name()).vid();
				break;
			}
			dyscopeId = state.getParentId(dyscopeId);
		}
		if (dyscopeId != -1 && vid != -1)
			varVal = state.getVariableValue(dyscopeId, vid);
		else {
			this.errorLogger.logSimpleError(
					expression.getSource(),
					state,
					process,
					symbolicAnalyzer.stateToString(state),
					ErrorKind.OTHER,
					"Remote access failure: The remote variable "
							+ varExpr.toString()
							+ "doesn't reachable by the remote process:"
							+ remotePid);
			throw new UnsatisfiablePathConditionException();
		}
		if (varVal == null)
			throw new UnsatisfiablePathConditionException();
		eval = new Evaluation(state, varVal);
		return eval;
	}

	/**
	 * Override for adding contract specific operations evaluating
	 * implementations.
	 */
	@Override
	protected Evaluation evaluateUnary(State state, int pid,
			UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		UNARY_OPERATOR unaryOp = expression.operator();
		String process = state.getProcessState(pid).name() + "(id = " + pid
				+ ")";

		switch (unaryOp) {
		case VALID:
			return this.evaluateValidOperatorExpression(state, pid, process,
					expression);
		default:
			return super.evaluateUnary(state, pid, expression);
		}
	}

	/**
	 * <p>
	 * <b>Summary:</b> Evaluating a {@link UnaryExpression} whose operator is
	 * {@link UNARY_OPERATOR#VALID} to true or false.
	 * </p>
	 * 
	 * <p>
	 * <b>Details:</b> A valid expression \valid( ptr_set ) takes one parameter
	 * ptr_set which has a pointer set type. Explanation for expressions have
	 * pointer set types can be found at {@link PointerSetExpression}. The
	 * evaluation on a valid expression \valid(ptr_set) is true only if all
	 * pointers p in ptr_set is dereferable.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param expression
	 *            The {@link UnaryExpression}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateValidOperatorExpression(State state, int pid,
			String process, UnaryExpression expression)
			throws UnsatisfiablePathConditionException {
		// Currently a pointer set expression is either a singleton set which is
		// a pointer, or a pointer plus a range:
		PointerSetExpression mem = (PointerSetExpression) expression.operand();
		Evaluation eval;
		SymbolicExpression pointer, range;
		NumericExpression low, high;
		IntegerNumber lowInt, highInt;
		Reasoner reasoner;
		boolean result = true;

		eval = this.evaluate(state, pid, mem.getBasePointer());
		state = eval.state;
		pointer = eval.value;
		// range must be concrete if it isn't null:
		if (mem.getRange() != null) {
			eval = evaluate(state, pid, mem.getRange());
			state = eval.state;
			range = eval.value;
			low = symbolicUtil.getLowOfRegularRange(range);
			high = symbolicUtil.getHighOfRegularRange(range);
		} else {
			low = universe.zeroInt();
			high = universe.zeroInt();
		}
		reasoner = universe.reasoner(state.getPathCondition());
		lowInt = (IntegerNumber) reasoner.extractNumber(low);
		highInt = (IntegerNumber) reasoner.extractNumber(high);
		if (lowInt == null || highInt == null) {
			// It's possible that at this time, pointer is allocated but the
			// length is still non-concrete. The current restrictions on \valid
			// (PointerSetExpression) expressions guarantees the following check
			// makes sense. At the time that the range is not concrete, there
			// are only two cases: 1. The base pointer is not valid, it is not
			// dereferable; 2. The base pointer is valid, then the base pointer
			// must point to some memory heap object, thus
			// "base pointer + high bound of the range" should be valid, i.e.
			// dereferable.
			eval = this.evaluatePointerAdd(state, process, pointer, high,
					false, mem.getSource()).left;
			if (symbolicAnalyzer.isDerefablePointer(state, pointer).right != ResultType.YES
					|| symbolicAnalyzer.isDerefablePointer(state, eval.value).right != ResultType.YES)
				result = false;
			else
				result = true;
		} else if (pointer.operator().equals(SymbolicOperator.TUPLE)) {
			if (lowInt.intValue() > highInt.intValue())
				throw new CIVLSyntaxException(
						"A range in \\valid must has a step with value one.");
			for (int i = lowInt.intValue(); i <= highInt.intValue(); i++) {
				eval = evaluatePointerAdd(state, process, pointer,
						universe.integer(i), false, expression.getSource()).left;
				state = eval.state;
				if (symbolicAnalyzer.isDerefablePointer(state, eval.value).right != ResultType.YES)
					result = false;
			}
		} else
			result = false;
		if (!result) {
			errorLogger.logSimpleError(
					expression.getSource(),
					state,
					process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.CONTRACT,
					"Cannot prove "
							+ symbolicAnalyzer.expressionEvaluation(state, pid,
									expression, true));
		}
		return new Evaluation(state, universe.bool(result));
	}

	/**
	 * Override for handling non-concrete symbolic pointers: The current policy
	 * for symbolic pointers does not allow dereferencing a symbolic pointer.
	 */
	@Override
	protected Evaluation evaluateDereference(State state, int pid,
			String process, DereferenceExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer;
		Evaluation eval;

		eval = this.evaluate(state, pid, expression.pointer());
		state = eval.state;
		pointer = eval.value;
		if (pointer.operator().equals(SymbolicOperator.LAMBDA)) {
			errorLogger
					.logSimpleError(expression.getSource(), state, process,
							symbolicAnalyzer.stateToString(state),
							ErrorKind.CONTRACT,
							"Attempt to dereference a pointer which cannot be proved as a valid pointer.");
			throw new UnsatisfiablePathConditionException();
		} else
			return super.evaluateDereference(state, pid, process, expression);
	}

	/**
	 * <p>
	 * <b>Summary:</b> Evaluates a function guard expression. When the function
	 * is contracted, the guard of the function relates to synchronization
	 * requirements specified in the function contracts, it they exist. For
	 * synchronization requirements, see {@link LibmpiEvaluator}.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b>The semantics of evaluating a function guard is :
	 * <ol>
	 * <li>If the function is contracted, using contracts as the guard of the
	 * function. e.g. sunchronization requirements.</li>
	 * <li>If the function is not contracted but is a system function, loads the
	 * library to evaluate the guard.</li>
	 * <li>If the function neither contracted nor a system function, the guard
	 * is simply true.</li>
	 * </ol>
	 * </p>
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The {@link FunctionGuardExpression} which represents a guard
	 *            for a specific function.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@Override
	protected Evaluation evaluateFunctionGuard(State state, int pid,
			String process, FunctionGuardExpression expression)
			throws UnsatisfiablePathConditionException {
		Triple<State, CIVLFunction, Integer> eval = this
				.evaluateFunctionIdentifier(state, pid,
						expression.functionExpression(), expression.getSource());
		CIVLFunction function;

		state = eval.first;
		function = eval.second;
		if (function == null) {
			errorLogger.logSimpleError(expression.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"function body cann't be found");
			throw new UnsatisfiablePathConditionException();
		}
		// If function is contracted, using contracts as guard:
		if (function.isContracted()) {
			return evaluateMPIWaitsfor(state, pid, process,
					function.functionContract(), function);
		}
		// If function is not contracted but is a system function, loads library
		// to evaluate the guard:
		if (function.isSystemFunction()) {
			SystemFunction systemFunction = (SystemFunction) function;

			return getSystemGuard(expression.getSource(), state, pid,
					systemFunction.getLibrary(), systemFunction.name().name(),
					expression.arguments());
		}
		// If function is not contracted and not a system function, the guard is
		// simply true:
		return new Evaluation(state, universe.trueExpression());
	}

	/**
	 * <p>
	 * <b>Summary</b> Loading MPI library evaluator to evaluate an MPI Contract
	 * expression ({@link MPIContractExpression}). see
	 * {@link LibmpiEvaluator#evaluateMPIContractExpression(State, int, String, MPIContractExpression)}
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The {@link MPIContractExpression}
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) this.libLoader
					.getLibraryEvaluator("mpi", this, modelFactory,
							symbolicUtil, this.symbolicAnalyzer);
			return mpiEvaluator.evaluateMPIContractExpression(state, pid,
					process, expression);
		} catch (LibraryLoaderException e) {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"unable to load the library evaluator for the library "
							+ "mpi" + " for the MPI expression " + expression);
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * <p>
	 * <b>Summary: </b>Evaluates expressions in a partial collective way. More
	 * information of collective evaluation and partial collective evaluation
	 * can be found at {@link LibmpiEvaluator}
	 * </p>
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param expression
	 * @param mpiComm
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation synchronizedEvaluate(State state, int pid, String process,
			Expression expression, Expression mpiComm)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) this.libLoader
					.getLibraryEvaluator("mpi", this, modelFactory,
							symbolicUtil, this.symbolicAnalyzer);
			return mpiEvaluator.partialCollectiveEvaluate(state, pid, process,
					expression, mpiComm);
		} catch (LibraryLoaderException e) {
			this.errorLogger.logSimpleError(expression.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"unable to load the library evaluator for the library "
							+ "mpi" + " for the expression " + expression);
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * <p>
	 * <b>Summary: </b>Loading MPI library evaluator to evaluate MPI waitsfor
	 * clauses specified in contracts. see
	 * {@link LibmpiEvaluator#evaluateMPIWaitsfor(State, int, String, FunctionContract, CIVLFunction)}
	 * </P>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The current PID
	 * @param process
	 *            The String identifier of the process
	 * @param contracts
	 *            The {@link FunctionContracts} of the given function
	 * @param function
	 *            The function who owns the function contracts
	 * @return A boolean expression which indicates whether the aforementioned
	 *         conditions are satisfied.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIWaitsfor(State state, int pid,
			String process, FunctionContract contracts, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		LibmpiEvaluator mpiEvaluator;

		try {
			mpiEvaluator = (LibmpiEvaluator) this.libLoader
					.getLibraryEvaluator("mpi", this, modelFactory,
							symbolicUtil, this.symbolicAnalyzer);
			return mpiEvaluator.evaluateMPIWaitsfor(state, pid, process,
					contracts, function);
		} catch (LibraryLoaderException e) {
			this.errorLogger.logSimpleError(contracts.getSource(), state,
					process, symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY,
					"Unable to load the library evaluator for the library: "
							+ "mpi to evaluateg the waitsfor clauses of "
							+ function);
			throw new UnsatisfiablePathConditionException();
		}
	}
}
