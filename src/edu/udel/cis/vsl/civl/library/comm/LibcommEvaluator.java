package edu.udel.cis.vsl.civl.library.comm;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;

public class LibcommEvaluator extends BaseLibraryEvaluator
		implements
			LibraryEvaluator {

	public static final int messageBufferField = 3;
	public static final int gcommHandleInCommField = 1;
	// private final NumericExpression wildSrcValue = universe.integer(-1);
	private final NumericExpression wildTagValue = universe.integer(-2);

	/* **************************** Constructors *************************** */

	public LibcommEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);
	}

	/*
	 * ********************* Methods from LibraryEvaluator *******************
	 */

	// @Override
	// public Evaluation evaluateGuard(CIVLSource source, State state, int pid,
	// String function, Expression[] arguments)
	// throws UnsatisfiablePathConditionException {
	// SymbolicExpression[] argumentValues;
	// int numArgs;
	// BooleanExpression guard;
	//
	// numArgs = arguments.length;
	// argumentValues = new SymbolicExpression[numArgs];
	// for (int i = 0; i < numArgs; i++) {
	// Evaluation eval = null;
	//
	// try {
	// eval = evaluator.evaluate(state, pid, arguments[i]);
	// } catch (UnsatisfiablePathConditionException e) {
	// // the error that caused the unsatifiable path condition should
	// // already have been reported.
	// return new Evaluation(state, universe.falseExpression());
	// }
	// argumentValues[i] = eval.value;
	// state = eval.state;
	// }
	// switch (function) {
	// // case "$comm_dequeue":
	// // try {
	// // guard = getDequeueGuard(state, pid, process, arguments,
	// // argumentValues, source);
	// // } catch (UnsatisfiablePathConditionException e) {
	// // // the error that caused the unsatifiable path condition should
	// // // already have been reported.
	// // return new Evaluation(state, universe.falseExpression());
	// // }
	// // break;
	// default:
	// guard = universe.trueExpression();
	// }
	// return new Evaluation(state, guard);
	// }

	/* *************************** Private Methods ************************* */

	/**
	 * <p>
	 * Return a boolean expression represents the guard of the function
	 * <code>$comm_dequeue(comm, source, tag)</code>. If is hard to decide
	 * weather source is wild card or not, add all possible situations into the
	 * returned guard (ditto for tag). e.g. (source is wild card -->(imply)
	 * ture) && (source is not wild card --> (imply) false)
	 * </p>
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The process id
	 * @param arguments
	 *            Expressions of arguments of the "$comm_dequeue()"function:
	 *            $comm, source, tag.
	 * @param argumentValues
	 *            Symbolic Expressions of arguments of the
	 *            "$comm_dequeue()"function.
	 * @return A predicate which is the guard of the function $comm_dequeue().
	 * @throws UnsatisfiablePathConditionException
	 */
	@SuppressWarnings("unused")
	private BooleanExpression getDequeueGuard(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource dequeueSource)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		NumericExpression source = (NumericExpression) argumentValues[1];
		NumericExpression tag = (NumericExpression) argumentValues[2];
		SymbolicExpression comm, gcomm, gcommHandle;
		NumericExpression dest;
		BooleanExpression guard;
		CIVLSource civlsource = arguments[0].getSource();
		CIVLType commType = typeFactory
				.systemType(ModelConfiguration.COMM_TYPE);
		Evaluation eval;
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		Number srcNum, destNum;
		int srcInt, destInt;

		eval = evaluator.dereference(civlsource, state, process, commHandle,
				false, true);
		state = eval.state;
		comm = eval.value;
		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false, true);
		state = eval.state;
		gcomm = eval.value;
		dest = (NumericExpression) universe.tupleRead(comm, zeroObject);
		if ((srcNum = reasoner.extractNumber(source)) != null)
			srcInt = ((IntegerNumber) srcNum).intValue();
		else
			throw new CIVLInternalException(
					"Cannot dequeue a message with a non-concrete source",
					arguments[1].getSource());
		destNum = reasoner.extractNumber(dest);
		assert destNum != null : "destionation of comm_dequeue cannot be null.";
		destInt = ((IntegerNumber) destNum).intValue();
		guard = dequeueGuardGenerator(civlsource, state, gcomm, srcInt, destInt,
				(NumericExpression) tag);
		return guard;
	}

	/**
	 * <p>
	 * Combining the given predicates and the results of evaluation on those
	 * predicates for the <code>$comm_dequeue()</code>.
	 * </p>
	 * 
	 * @author Ziqing Luo
	 * @param civlsource
	 *            The CIVL program source of the statement.
	 * @param state
	 *            Current state
	 * @param predicates
	 *            The set of predicates
	 * @param gcomm
	 *            The global communicator
	 * @param source
	 *            The source from where "$comm_dequeue" receives messages.
	 * @param dest
	 *            The destination which is the receiver itself
	 * @param tag
	 *            The message tag
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BooleanExpression dequeueGuardGenerator(CIVLSource civlsource,
			State state, SymbolicExpression gcomm, int source, int dest,
			NumericExpression tag) throws UnsatisfiablePathConditionException {
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		boolean hasMsg, isWildTag = false;

		/*
		 * Any call on $comm_dequeue should make sure the tag is deterministic
		 * at the call point, i.e. the tag is either can be determined to be a
		 * wild-card tag or any other symbolic values:
		 */
		if (reasoner.isValid(universe.equals(tag, wildTagValue)))
			isWildTag = true;
		hasMsg = !getAllPossibleSources(state, reasoner, gcomm, source, dest,
				tag, isWildTag, civlsource).isEmpty();
		return universe.bool(hasMsg);

	}

	/*
	 * *********************** Public helper functions ***********************
	 */
	/**
	 * Seeks all possible channels of the given communicator for all available
	 * sources whose corresponding channel (which is decided by "destination"
	 * which is the process itself and the "source") contains at least one
	 * message with a satisfied tag.
	 * 
	 * @param state
	 *            The current state
	 * @param reasoner
	 *            The reasoner used to evaluate concrete numbers
	 * @param gcomm
	 *            The symbolic expression of a global communicator object
	 * @param source
	 *            The integer type source number
	 * @param tag
	 *            The integer type tag number
	 * @param dest
	 *            The integer type destination number
	 * @param civlsource
	 * @return A list of all available sources
	 * @throws UnsatisfiablePathConditionException
	 */
	public List<NumericExpression> getAllPossibleSources(State state,
			Reasoner reasoner, SymbolicExpression gcomm, int source,
			int destination, NumericExpression tag, boolean isWildTag,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		SymbolicExpression buf, bufRow, queue;
		SymbolicExpression messages = null, message = null;
		NumericExpression src = universe.integer(source);
		NumericExpression dest = universe.integer(destination);
		NumericExpression queueLength;
		List<NumericExpression> results = new LinkedList<>();

		buf = universe.tupleRead(gcomm, threeObject);
		assert (source == -1
				|| source >= 0) : "Message source is neither wild-card nor valid positive integer.\n";
		// non-wild card source and tag
		if (source >= 0 && !isWildTag) {
			Number numQueLength;
			int intQueLength;

			bufRow = universe.arrayRead(buf, src);
			queue = universe.arrayRead(bufRow, dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = (NumericExpression) universe.tupleRead(queue,
					zeroObject);
			numQueLength = reasoner.extractNumber(queueLength);
			assert numQueLength != null : "Length of message queue is expected to be concrete.\n";
			assert numQueLength instanceof IntegerNumber : "Length of message queue must be able to cast to an IntegerNumber object.\n";
			intQueLength = ((IntegerNumber) numQueLength).intValue();
			for (int i = 0; i < intQueLength; i++) {
				message = universe.arrayRead(messages, universe.integer(i));
				if (reasoner.isValid(universe
						.equals(universe.tupleRead(message, twoObject), tag))) {
					results.add(src);
					return results;
				}
			}
		} // non-wild card source and any_tag
		else if (source >= 0 && isWildTag) {
			bufRow = universe.arrayRead(buf, src);
			queue = universe.arrayRead(bufRow, dest);
			messages = universe.tupleRead(queue, oneObject);
			queueLength = (NumericExpression) universe.tupleRead(queue,
					zeroObject);
			if (reasoner.isValid(
					universe.lessThan(zero, (NumericExpression) queueLength)))
				results.add(src);
			return results;
		} // any source and non-wild card tag
		else if (source == -1 && !isWildTag) {
			Number numNprocs, numQueLength;
			int intNumNprocs, intNumQueLength;
			NumericExpression nprocs = (NumericExpression) universe
					.tupleRead(gcomm, zeroObject);

			numNprocs = reasoner.extractNumber(nprocs);
			assert numNprocs != null : "The number of processes in communicator is expected to be concrete.\n";
			assert numNprocs instanceof IntegerNumber : "The number of processes in communicator must be able to cast to an IntegerNumber object.\n";
			intNumNprocs = ((IntegerNumber) numNprocs).intValue();
			for (int i = 0; i < intNumNprocs; i++) {
				NumericExpression currProc = universe.integer(i);

				bufRow = universe.arrayRead(buf, currProc);
				queue = universe.arrayRead(bufRow, dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = (NumericExpression) universe.tupleRead(queue,
						zeroObject);
				numQueLength = reasoner.extractNumber(queueLength);
				assert numQueLength != null : "Length of message queue is expected to be concrete.\n";
				assert numQueLength instanceof IntegerNumber : "Length of message queue must be able to cast to an IntegerNumber object.\n";
				intNumQueLength = ((IntegerNumber) numQueLength).intValue();
				for (int j = 0; j < intNumQueLength; j++) {
					BooleanExpression tagMatchClaim;

					message = universe.arrayRead(messages, universe.integer(j));
					tagMatchClaim = universe.equals(
							universe.tupleRead(message, twoObject), tag);
					if (reasoner.isValid(tagMatchClaim)) {
						results.add(currProc);
						break;
					}
				}
			}
			return results;
		} // wild card source and wild card tag
		else if (source == -1 && isWildTag) {
			Number numNprocs;
			int intNumNprocs;
			NumericExpression nprocs = (NumericExpression) universe
					.tupleRead(gcomm, zeroObject);

			numNprocs = reasoner.extractNumber(nprocs);
			assert numNprocs != null : "The number of processes in communicator is expected to be concrete.\n";
			assert numNprocs instanceof IntegerNumber : "The number of processes in communicator must be able to cast to an IntegerNumber object.\n";
			intNumNprocs = ((IntegerNumber) numNprocs).intValue();
			for (int i = 0; i < intNumNprocs; i++) {
				NumericExpression currProc = universe.integer(i);

				bufRow = universe.arrayRead(buf, currProc);
				queue = universe.arrayRead(bufRow, dest);
				messages = universe.tupleRead(queue, oneObject);
				queueLength = (NumericExpression) universe.tupleRead(queue,
						zeroObject);
				if (reasoner.isValid(universe.lessThan(zero,
						(NumericExpression) queueLength)))
					results.add(currProc);
			}
			return results;
		}
		return results;
	}

	/**
	 * Return the {@link Evaluation} of $gcomm object by giving a
	 * {@link SymbolicExpression} of $comm object.
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param process
	 *            the string identifier of the process
	 * @param comm
	 *            the {@link SymbolicExpression} of $comm object
	 * @param civlsource
	 *            the {@link CIVLSource} of the $comm object
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation getGcommByComm(State state, int pid, String process,
			SymbolicExpression comm, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gcommHandle;
		Evaluation eval;

		gcommHandle = universe.tupleRead(comm, oneObject);
		eval = evaluator.dereference(civlsource, state, process, gcommHandle,
				false, true);
		return eval;
	}

	/**
	 * Return the {@link Evaluation} of $comm object by giving a
	 * {@link Expression} of a $comm handle.
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param process
	 *            the string identifier of the process
	 * @param commHandleExpr
	 *            the {@link Expression} of a $comm handle
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation getCommByCommHandleExpr(State state, int pid,
			String process, Expression commHandleExpr)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle;
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, commHandleExpr);
		commHandle = eval.value;
		eval = evaluator.dereference(commHandleExpr.getSource(), eval.state,
				process, commHandle, false, true);
		return eval;
	}

	/**
	 * A wrapper function for read $proc array in a communicator. Any out of
	 * bound error should reported consistently.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param procArray
	 *            The {@link SymbolicExpression} of the $proc array
	 * @param index
	 *            The array reading index
	 * @param source
	 *            The CIVLSource of the place that the array reading action
	 *            happens
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public SymbolicExpression readProcArray(State state, int pid,
			String process, SymbolicExpression procArray,
			NumericExpression index, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		BooleanExpression claim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition(universe));
		ResultType resultType;

		claim = universe.lessThan(index, universe.length(procArray));
		resultType = reasoner.valid(claim).getResultType();
		if (!resultType.equals(ResultType.YES)) {
			state = this.errorLogger.logError(source, state, pid,
					symbolicAnalyzer.stateInformation(state), claim, resultType,
					ErrorKind.OUT_OF_BOUNDS, "The place of " + process
							+ " in a communicator is out of the bound of the total number of processes");
			throw new UnsatisfiablePathConditionException();
		}
		return universe.arrayRead(procArray, index);
	}
}
