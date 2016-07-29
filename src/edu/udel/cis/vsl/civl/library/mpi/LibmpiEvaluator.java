package edu.udel.cis.vsl.civl.library.mpi;

import java.util.BitSet;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression.ExpressionKind;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

/**
 * <p>
 * <b>Summary</b> This class is an evaluator for evaluating expressions with MPI
 * specific semantics, including (partial) collective evaluation, semantics of
 * {@link MPIContractExpression}s and snap-shooting etc.
 * </p>
 * 
 * <p>
 * (Partial) Collective evaluation is an approach of evaluating expressions that
 * involving variables come from different MPI processes. Although it is one of
 * the most well-known feature of MPI that there is no shared storage between
 * any pair of MPI processes, one can use some auxiliary variables to expression
 * properties that involving a set of MPI processes and prove if they holds.
 * 
 * <ul>
 * <li><b>Collective evaluation c[E, comm, merge, Sp]:</b> A collective
 * evaluation is a tuple: a set of expressions E, an MPI communicator comm ,a
 * function merge(Sp) which maps a set of snapshots Sp to a state s and a set of
 * snapshots Sp. The MPI communicator comm associates to a set of MPI processes
 * P, for each process p in P, it matches a unique snapshot sp in Sp. Thus |Sp|
 * == |P|. The result of the collective evaluation is a set of symbolic values.
 * </li>
 * 
 * <li><b>Partial collective evaluation pc[E, comm, merge', Sp', s]:</b> A
 * partial collective evaluation is a tuple, in addition to the 4 elements of
 * c[E, comm, merge', Sp'], there is one more which is the current state s.
 * Compare to collective evaluation, there are some constraints: the function
 * merge'(Sp', s) maps a set of snapshots Sp' and a state s to a merged state
 * s'. Snapshots in Sp' are committed by the set of processes P', P' is a subset
 * of P. There exists one process set P'' which is also a subset of P. P' and
 * P'' are disjoint, the union of P' and P'' equals to P. s' consists of all
 * snapshots in Sp' and another set of snapshots Sp'' taken on s for processes
 * in P''. The result of the collective evaluation is a set of symbolic values.
 * .</li>
 * 
 * <li><b>Synchronization requirements [WP, a, comm, l]:</b>A synchronization
 * requirement is a tuple: A set of MPI processes WP, an assumption a , an MPI
 * communicator comm and a program location l. It expresses such a
 * synchronization property: It current process satisfies assumption a, the
 * current process can not keep executing until all processes in WP have reached
 * the location l. WP must be a subset of P which is associated to comm.</li>
 * </ul>
 * </p>
 * 
 * 
 * @author ziqingluo
 *
 */
public class LibmpiEvaluator extends BaseLibraryEvaluator
		implements
			LibraryEvaluator {
	public static int p2pCommField = 0;
	public static int colCommField = 1;
	public final IntObject queueIDField = universe.intObject(4);
	public final NumericExpression p2pCommIndexValue = zero;
	public final NumericExpression colCommIndexValue = one;

	public LibmpiEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);

	}

	public static Pair<CIVLPrimitiveType, NumericExpression> mpiTypeToCIVLType(
			SymbolicUniverse universe, CIVLTypeFactory typeFactory,
			int MPI_TYPE, CIVLSource source) {
		CIVLPrimitiveType primitiveType;
		NumericExpression count = universe.oneInt();

		switch (MPI_TYPE) {
			case 0 : // char
				primitiveType = typeFactory.charType();
				break;
			case 1 : // character
				primitiveType = typeFactory.charType();
				break;
			case 8 : // int
				primitiveType = typeFactory.integerType();
				break;
			case 20 : // long
				primitiveType = typeFactory.integerType();
				break;
			case 22 : // float
				primitiveType = typeFactory.realType();
				break;
			case 23 : // double
				primitiveType = typeFactory.realType();
				break;
			case 24 : // long double
				primitiveType = typeFactory.realType();
				break;
			case 27 : // long long
				primitiveType = typeFactory.integerType();
				break;
			case 39 : // 2int
				primitiveType = typeFactory.integerType();
				count = universe.integer(2);
				break;
			default :
				throw new CIVLUnimplementedFeatureException(
						"CIVL doesn't have such a CIVLPrimitiveType", source);
		}
		return new Pair<>(primitiveType, count);
		/*
		 * MPI_CHAR, MPI_CHARACTER, MPI_SIGNED_CHAR, MPI_UNSIGNED_CHAR,
		 * MPI_BYTE, MPI_WCHAR, MPI_SHORT, MPI_UNSIGNED_SHORT, MPI_INT,
		 * MPI_INT16_T, MPI_INT32_T, MPI_INT64_T, MPI_INT8_T, MPI_INTEGER,
		 * MPI_INTEGER1, MPI_INTEGER16, MPI_INTEGER2, MPI_INTEGER4,
		 * MPI_INTEGER8, MPI_UNSIGNED, MPI_LONG, MPI_UNSIGNED_LONG, MPI_FLOAT,
		 * MPI_DOUBLE, MPI_LONG_DOUBLE, MPI_LONG_LONG_INT,
		 * MPI_UNSIGNED_LONG_LONG, MPI_LONG_LONG, MPI_PACKED, MPI_LB, MPI_UB,
		 * MPI_UINT16_T, MPI_UINT32_T, MPI_UINT64_T, MPI_UINT8_T, MPI_FLOAT_INT,
		 * MPI_DOUBLE_INT, MPI_LONG_INT, MPI_SHORT_INT, MPI_2INT,
		 * MPI_LONG_DOUBLE_INT, MPI_AINT, MPI_OFFSET, MPI_2DOUBLE_PRECISION,
		 * MPI_2INTEGER, MPI_2REAL, MPI_C_BOOL, MPI_C_COMPLEX,
		 * MPI_C_DOUBLE_COMPLEX, MPI_C_FLOAT_COMPLEX, MPI_C_LONG_DOUBLE_COMPLEX,
		 * MPI_COMPLEX, MPI_COMPLEX16, MPI_COMPLEX32, MPI_COMPLEX4,
		 * MPI_COMPLEX8, MPI_REAL, MPI_REAL16, MPI_REAL2, MPI_REAL4, MPI_REAL8
		 */
	}

	/**************************** Contract section ****************************/
	/**
	 * <p>
	 * <b>Summary:</b> Evaluates an {@link MPIContractExpression}.
	 * </p>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The PID of the process.
	 * @param process
	 *            The String identifier of the process.
	 * @param expression
	 *            The MPIContractExpression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation evaluateMPIContractExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		MPI_CONTRACT_EXPRESSION_KIND mpiContractKind = expression
				.mpiContractKind();

		switch (mpiContractKind) {
			case MPI_EMPTY_IN :
				return evaluateMPIEmptyExpression(state, pid, process,
						expression, false);
			case MPI_EMPTY_OUT :
				return evaluateMPIEmptyExpression(state, pid, process,
						expression, true);
			case MPI_AGREE :
				return evaluateMPIAgreeExpression(state, pid, process,
						expression);
			case MPI_EQUALS :
				return evaluateMPIEqualsExpression(state, pid, process,
						expression);
			default :
				throw new CIVLInternalException("Unreachable",
						expression.getSource());
		}
	}

	/**
	 * <p>
	 * <b>Notes for pre-condition:</b> This method doesn't requires that all
	 * DESIRED processes already committed their snapshots, this should be
	 * guaranteed by the caller of this method.
	 * </p>
	 * <p>
	 * <b>Summary:</b> Partial collective evaluation on a set of expressions E.
	 * </p>
	 * <p>
	 * <b>Details:</b> This method first looks for a corresponding WAITSFOR
	 * collective entry. If e exists, the evaluation of the expression happens
	 * on a merged state s which consists of all saved snapshots in entry.
	 * Snapshots of unrecorded processes are taken from the current state. If e
	 * not exists, a state s' will be created by replacing PIDs with Places of
	 * processes in MPI communicator in the current state.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The expression e in E that will evaluate (partial)
	 *            collectively.
	 * @param mpiComm
	 *            The MPI communicator associates to this partial collective
	 *            evaluation.
	 * @return The results of the evaluation.
	 * @throws UnsatisfiablePathConditionException
	 */
	public Evaluation partialCollectiveEvaluate(State state, int pid,
			String process, Expression expression, Expression mpiComm)
			throws UnsatisfiablePathConditionException {
		// Find out the top unrecorded WAITSFOR entry first, it no such entry,
		// just do regular evaluation:
		Evaluation eval = evaluator.evaluate(state, pid, mpiComm);
		Pair<NumericExpression, NumericExpression> place_queueId;
		ImmutableCollectiveSnapshotsEntry[] queue;
		ImmutableCollectiveSnapshotsEntry entry = null;
		SymbolicExpression mpiCommVal;
		boolean foundEntry = false;
		int place, queueId;
		int[] place2Pids;
		Pair<SymbolicExpression, Integer> procArray;

		state = eval.state;
		mpiCommVal = eval.value;
		place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
				mpiComm, mpiCommVal, mpiComm.getSource());
		place = ((IntegerNumber) universe.extractNumber(place_queueId.left))
				.intValue();
		queueId = ((IntegerNumber) universe.extractNumber(place_queueId.right))
				.intValue();
		queue = stateFactory.getSnapshotsQueue(state, queueId);
		for (int i = 0; i < queue.length; i++) {
			entry = queue[i];
			if (entry.contractKind() == ContractKind.WAITSFOR
					&& !entry.isRecorded(place)) {
				foundEntry = true;
				break;
			}
		}
		procArray = getProcArrayFromMPIComm(state, pid, process, mpiComm,
				mpiCommVal, mpiComm.getSource());
		place2Pids = new int[procArray.right];
		for (int i = 0; i < procArray.right; i++) {
			place2Pids[i] = modelFactory.getProcessId(mpiComm.getSource(),
					universe.arrayRead(procArray.left, universe.integer(i)));
		}
		if (!foundEntry) {
			// if not found an entry, the state still needs to be modified so
			// that PIDs in it are same as places in MPI communicators:
			State evalState = stateFactory.updateProcessesForState(state,
					place2Pids);

			eval = evaluator.evaluate(evalState, place, expression);
			eval.state = state;
			return eval;
		} else {
			State mergedState;

			mergedState = stateFactory.partialMergeMonostates(state, entry,
					place2Pids);
			eval = evaluator.evaluate(mergedState, place, expression);
			eval.state = state;
			return eval;
		}
	}

	/**
	 * <p>
	 * <b>Summary:</b> Evaluates whether all "waitsfor" clauses specified in the
	 * {@link FunctionContract} are satisfied at the current state for the
	 * current process.
	 * </p>
	 * 
	 * <p>
	 * <b>Details:</b> "waitsfor" clauses specifies a set of MPI processes WP
	 * that the current process needs to wait before it can continue executing.
	 * The evaluation on "waitsfor" clauses is partial collective evaluation:
	 * <ol>
	 * <li>If there is no "waitsfor" clause corresponding to the current process
	 * (there is no "waitsfor" clause or they are under a named-behavior whose
	 * assumption is unsatisfied for the current process), the evaluation is
	 * true.</li>
	 * <li>Else if there is only one MPI process wp denoted by all corresponding
	 * "waitsfor" clauses and <code>wp == current process</code>, the evaluation
	 * is true.</li>
	 * <li>Else if there is a "WAITSFOR" collective entry in the snapshot queue
	 * and a set of MPI processes P has been recorded on the entry. If
	 * <code>P == WP</code>, the evaluation is true</li>
	 * <li>Otherwise, the evaluation is false.</li>
	 * </ol>
	 * </p>
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
	public Evaluation evaluateMPIWaitsfor(State state, int pid, String process,
			FunctionContract contracts, CIVLFunction function)
			throws UnsatisfiablePathConditionException {
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		boolean result = true;
		Evaluation eval;

		// found the entry first:
		for (MPICollectiveBehavior collective : contracts.getMPIBehaviors()) {
			Pair<NumericExpression, NumericExpression> place_queueId;
			int place, queueId;
			CollectiveSnapshotsEntry[] queue;
			CollectiveSnapshotsEntry entry = null;
			boolean foundEntry = false;
			boolean subResult = true;
			BitSet wfClausesInCollective;
			Expression MPIComm = collective.communicator();

			eval = evaluator.evaluate(state, pid, MPIComm);
			state = eval.state;
			place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
					MPIComm, eval.value, MPIComm.getSource());
			place = ((IntegerNumber) reasoner
					.extractNumber((NumericExpression) place_queueId.left))
							.intValue();
			queueId = ((IntegerNumber) reasoner
					.extractNumber((NumericExpression) place_queueId.right))
							.intValue();
			queue = stateFactory.getSnapshotsQueue(state, queueId);
			for (int i = 0; i < queue.length; i++) {
				entry = queue[i];
				if (entry.contractKind() == ContractKind.WAITSFOR
						&& !entry.isRecorded(place)) {
					foundEntry = true;
					break;
				}
			}
			wfClausesInCollective = getWaitsforPlacesIn(collective, state, pid);
			if (wfClausesInCollective.cardinality() == 0)
				continue;
			if (wfClausesInCollective.cardinality() == 1
					&& place == wfClausesInCollective.nextSetBit(0))
				continue;
			if (foundEntry) {
				for (int i = wfClausesInCollective.nextSetBit(
						0); i >= 0; i = wfClausesInCollective.nextSetBit(i + 1))
					subResult &= entry.isRecorded(i) || i == place;
				result &= subResult;
			} else
				// If there is no entry (and the current process is not the only
				// waited one), blocks:
				return new Evaluation(state, universe.falseExpression());
			if (!result)
				return new Evaluation(state, universe.falseExpression());
		}
		return new Evaluation(state, universe.bool(result));
	}

	/**
	 * <p>
	 * <b>Summary: </b> Evaluates \mpi_empty_in(int src) / \mpi_empty_out(int
	 * dest) expression (both accept wild card argument which means for all
	 * sources (src) or destinations (dest)).
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String of the process identifier
	 * @param expression
	 *            The {@link MPIContractExpression} expression
	 * @param isOut
	 *            flag indicates weather it's a \mpi_empty_out or \mpi_empty_in
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIEmptyExpression(State state, int pid,
			String process, MPIContractExpression expression, boolean isOut)
			throws UnsatisfiablePathConditionException {
		Expression communicator = expression.communicator();
		Expression argument = expression.arguments()[0];
		Evaluation eval;
		Pair<NumericExpression, NumericExpression> place_queueId;
		// The reason why the types of the values of the only argument and place
		// is array type is in case of wild-card argument which represents a set
		// of values:
		NumericExpression argVals[], place[], queueId;
		int queueIdInt;
		NumericExpression patternIndex = expression
				.getMpiCommunicationPattern() == MPICommunicationPattern.P2P
						? p2pCommIndexValue
						: colCommIndexValue;

		place = new NumericExpression[1];
		eval = evaluator.evaluate(state, pid, communicator);
		state = eval.state;
		place_queueId = getPlaceAndQueueIDFromMPIComm(state, pid, process,
				communicator, eval.value, communicator.getSource());
		place[0] = place_queueId.left;
		queueId = place_queueId.right;
		assert universe.extractNumber(queueId) != null;
		queueIdInt = ((IntegerNumber) universe.extractNumber(queueId))
				.intValue();
		assert argument.getExpressionType().isIntegerType();
		argVals = deterministicalizeMsgSourceOrDest(state, pid, queueIdInt,
				argument);
		if (isOut)
			return evaluateBufferEmptyExpression(state, pid, place, argVals,
					queueIdInt, patternIndex, expression.getSource());
		else
			return evaluateBufferEmptyExpression(state, pid, argVals, place,
					queueIdInt, patternIndex, expression.getSource());
	}

	/**
	 * <p>
	 * <b>Summary:</b> A helper method for
	 * {@link #evaluateMPIEmptyExpression(State, int, String, MPIContractExpression, boolean)}
	 * . This method has no idea about weather it's "empty_in" or "empty_out".
	 * </p>
	 * 
	 * @param state
	 *            The state on where the evaluation happens
	 * @param pid
	 *            The PID of the process
	 * @param msgSrcs
	 *            Values representing the source place, only one value if it's
	 *            not a wild-card
	 * @param msgDests
	 *            Values representing the destination place, only one value if
	 *            it's not a wild-card
	 * @param patternIndex
	 *            The index indicating which MPI communication pattern is the
	 *            message buffer belong to.
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateBufferEmptyExpression(State state, int pid,
			NumericExpression[] msgSrcs, NumericExpression[] msgDests,
			int queueId, NumericExpression patternIndex, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression msgBuffers;
		BooleanExpression claim = trueValue, subClaim;

		msgBuffers = stateFactory.peekCollectiveSnapshotsEntry(state, queueId)
				.getMsgBuffers();
		for (int i = 0; i < msgSrcs.length; i++)
			for (int j = 0; j < msgDests.length; j++, claim = universe
					.and(claim, subClaim))
				subClaim = messageBufferEmpty(state, msgSrcs[i], msgDests[j],
						msgBuffers, patternIndex);
		return new Evaluation(state, claim);
	}

	/**
	 * <p>
	 * <b>Summary:</b> A helper method. In case of the message source or
	 * destination expression e has a wild-card value, this helper method
	 * returns all deterministic values of e as an array.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param queueId
	 *            The Snapshots queue Id (A.K.A the index of a MPI
	 *            communicator).
	 * @param srcOrDest
	 *            The expression represents the message source or destionation.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private NumericExpression[] deterministicalizeMsgSourceOrDest(State state,
			int pid, int queueId, Expression srcOrDest)
			throws UnsatisfiablePathConditionException {
		NumericExpression results[];
		if (srcOrDest.expressionKind() == ExpressionKind.WILDCARD) {
			CollectiveSnapshotsEntry entry = stateFactory
					.peekCollectiveSnapshotsEntry(state, queueId);
			int nprocs = entry.numInvolvedProcesses();

			results = new NumericExpression[nprocs];
			for (int i = 0; i < nprocs; i++)
				results[i] = universe.integer(i);
		} else {
			Evaluation eval = evaluator.evaluate(state, pid, srcOrDest);

			assert srcOrDest.getExpressionType().isIntegerType();
			results = new NumericExpression[1];
			results[0] = (NumericExpression) eval.value;
		}
		return results;
	}

	/**
	 * <p>
	 * <b>Summary:</b> A helper method for generating a boolean expression which
	 * expresses the property that a message buffer, which specified by a given
	 * source, destination and communication pattern, is empty.
	 * </p>
	 * 
	 * @param state
	 *            The current state;
	 * @param msgSrc
	 *            The message source value
	 * @param msgDest
	 *            The message destination value;
	 * @param msgBuffers
	 *            The value of the whole message buffers (which is a matrix)
	 * @param patternIndex
	 *            The index indicating which MPI communication pattern is the
	 *            message buffer belong to.
	 * @return
	 */
	private BooleanExpression messageBufferEmpty(State state,
			NumericExpression msgSrc, NumericExpression msgDest,
			SymbolicExpression msgBuffers, NumericExpression patternIndex) {
		SymbolicExpression msgBuffer, msgChannel;
		BooleanExpression claim;

		msgBuffer = universe.arrayRead(msgBuffers, patternIndex);
		msgChannel = universe.arrayRead(universe.arrayRead(msgBuffer, msgSrc),
				msgDest);
		claim = universe.equals(universe.tupleRead(msgChannel, zeroObject),
				zero);
		return claim;
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The state is a collate state and the pid represents
	 * the process in the collate state. By looking at the call stack of a
	 * collate state, one can decide weather a process has committed its'
	 * snapshot to the collate state.
	 * </p>
	 * 
	 * <p>
	 * Let eval(e, p, s) denote the evaluation of expression e on process p in
	 * state s. There is a set P of processes in the collate state c that for
	 * each p in P, p has a non-empty call stack (i.e. process p has committed
	 * its snapshot), then <code> for all p_i and p_j in P (p_i != p_j),
	 * eval(expression, p_i, c) == eval(expression, p_j, c)
	 * </code>
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The current PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The \mpi_agree(expr) expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIAgreeExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		int nprocs = state.numProcs();
		BooleanExpression pred = universe.trueExpression();
		SymbolicExpression value;
		Evaluation eval;
		Expression expr = expression.arguments()[0];

		eval = evaluator.evaluate(state, pid, expr);
		state = eval.state;
		value = eval.value;
		for (int i = 0; i < nprocs; i++)
			if (i != pid && !state.getProcessState(i).hasEmptyStack()) {
				eval = evaluator.evaluate(state, i, expr);
				state = eval.state;
				pred = universe.and(pred, universe.equals(value, eval.value));
			}
		eval.state = state;
		eval.value = pred;
		return eval;
	}

	/**
	 * <p>
	 * An \mpi_region expression shall evaluate to an array of objects, the
	 * length of the array and the type of the objects are defined by the MPI
	 * type signiture: count and MPI_Datatype.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The current PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The \mpi_region(void *, int, MPI_Datatype) expression
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIRegion(State state, int pid, String process,
			MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression buf = expression.arguments()[0];
		Expression count = expression.arguments()[1];
		Expression datatype = expression.arguments()[2];
		SymbolicExpression bufVal, countVal, datatypeVal, data;
		int datatypeCode;
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, buf);
		state = eval.state;
		bufVal = eval.value;
		eval = evaluator.evaluate(state, pid, count);
		state = eval.state;
		countVal = eval.value;
		eval = evaluator.evaluate(state, pid, datatype);
		state = eval.state;
		datatypeVal = eval.value;

		// TODO: report error for non-concrete datatype
		datatypeCode = ((IntegerNumber) universe
				.extractNumber((NumericExpression) datatypeVal)).intValue();
		eval = getDataFrom(state, pid, process, buf, bufVal,
				(NumericExpression) countVal, true, false,
				expression.getSource());
		// TODO: check type consistency
		return eval;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Evaluates an MPI_EQUALS expression, it compares each
	 * elements of the given two memory objects. Currently it ignores the
	 * datatype checking (but not necessary if objects are checked as equal).
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param expression
	 *            The MPI_EQUALS expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIEqualsExpression(State state, int pid,
			String process, MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression values[] = new SymbolicExpression[4];
		Evaluation eval;
		SymbolicExpression result0, result1;
		BooleanExpression result;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int count;
		Number countNum;
		CIVLSource source = expression.getSource();

		// \mpi_equals() takes 4 arguments: pointer0, count, datatype, pointer1:
		for (int i = 0; i < 4; i++) {
			eval = evaluator.evaluate(state, pid, expression.arguments()[i]);
			state = eval.state;
			values[i] = eval.value;
		}
		countNum = reasoner.extractNumber((NumericExpression) values[1]);
		if (countNum == null)
			throw new CIVLInternalException(
					"Value of expression: " + expression.arguments()[2]
							+ "are expecting to be elaborated to concrete",
					expression.arguments()[2].getSource());
		count = ((IntegerNumber) countNum).intValue();
		// Offset = 0:
		eval = evaluator.dereference(source, state, process,
				expression.arguments()[0], values[0], false);
		result0 = eval.value;
		eval = evaluator.dereference(source, state, process,
				expression.arguments()[3], values[3], false);
		result1 = eval.value;
		result = universe.equals(result0, result1);
		// Offset > 0:
		for (int i = 1; i < count; i++) {
			eval = evaluator.evaluatePointerAdd(state, process, values[0],
					universe.integer(i), false, source).left;
			eval = evaluator.dereference(expression.getSource(), state, process,
					expression.arguments()[0], eval.value, false);
			result0 = eval.value;
			eval = evaluator.evaluatePointerAdd(state, process, values[3],
					universe.integer(i), false, source).left;
			eval = evaluator.dereference(expression.getSource(), state, process,
					expression.arguments()[3], eval.value, false);
			result1 = eval.value;
			result = universe.and(result, universe.equals(result0, result1));
		}
		return new Evaluation(state, result);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Helper method. Returns a union bit set of all waiting
	 * MPI processes specified by a {@link MPICollectiveBehavior}. If a set of
	 * waiting processes are specified under an unsatisfiable
	 * {@link NamedFunctionBehavior}, they will not be unioned.
	 * </p>
	 * 
	 * @param colBehav
	 *            The {@link MPICollectiveBehavior}
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private BitSet getWaitsforPlacesIn(MPICollectiveBehavior colBehav,
			State state, int pid) throws UnsatisfiablePathConditionException {
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		BitSet wfSet = new BitSet();
		Evaluation eval;

		if (!colBehav.getWaitsforList().isEmpty())
			for (Expression wfSetExpr : colBehav.getWaitsforList()) {
				eval = evaluator.evaluate(state, pid, wfSetExpr);
				state = eval.state;
				wfSet.or(symbolicUtil.range2BitSet(eval.value, reasoner));
			}
		for (NamedFunctionBehavior namedBehav : colBehav.namedBehaviors()) {
			BooleanExpression assumptionsVal;

			eval = evaluator.evaluate(state, pid, namedBehav.assumptions());
			state = eval.state;
			assumptionsVal = (BooleanExpression) eval.value;
			if (reasoner.isValid(assumptionsVal))
				if (!namedBehav.getWaitsforList().isEmpty()) {
					for (Expression wfSetExpr : namedBehav.getWaitsforList()) {
						eval = evaluator.evaluate(state, pid, wfSetExpr);
						state = eval.state;
						wfSet.or(symbolicUtil.range2BitSet(eval.value,
								reasoner));
					}
				}
		}
		return wfSet;
	}

	/**
	 * <p>
	 * <b>Summary:</b> A helper function: Returns the place field and the
	 * message buffer field by accessing through a $comm handle.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param MPIComm
	 *            The Expression of the MPI communicator handle
	 * @param MPICommVal
	 *            The Symbolic Expression of the MPI communicator handle
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<NumericExpression, NumericExpression> getPlaceAndQueueIDFromMPIComm(
			State state, int pid, String process, Expression MPIComm,
			SymbolicExpression MPICommVal, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression p2pComm, p2pCommHandle;
		NumericExpression place, queueID;

		queueID = (NumericExpression) universe.tupleRead(MPICommVal,
				queueIDField);
		p2pCommHandle = universe.tupleRead(MPICommVal, zeroObject);
		eval = evaluator.dereference(source, state, process, MPIComm,
				p2pCommHandle, false);
		state = eval.state;
		p2pComm = eval.value;
		place = (NumericExpression) universe.tupleRead(p2pComm, zeroObject);
		return new Pair<>(place, queueID);
	}

	/**
	 * <p>
	 * <b>Summary: </b> A helper method, returns a symbolic process array and
	 * the array length. The process array can be seen as a place-to-pid look up
	 * table.
	 * </p>
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param MPIComm
	 * @param MPICommVal
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<SymbolicExpression, Integer> getProcArrayFromMPIComm(
			State state, int pid, String process, Expression MPIComm,
			SymbolicExpression MPICommVal, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Evaluation eval;
		SymbolicExpression p2pComm, p2pCommHandle, gcomm;
		NumericExpression nprocs;
		int nprocsInt;

		p2pCommHandle = universe.tupleRead(MPICommVal, zeroObject);
		eval = evaluator.dereference(source, state, process, MPIComm,
				p2pCommHandle, false);
		state = eval.state;
		p2pComm = eval.value;
		eval = evaluator.dereference(source, state, process, MPIComm,
				universe.tupleRead(p2pComm, oneObject), false);
		state = eval.state;
		gcomm = eval.value;
		nprocs = (NumericExpression) universe.tupleRead(gcomm, zeroObject);
		nprocsInt = ((IntegerNumber) universe.extractNumber(nprocs)).intValue();
		return new Pair<>(universe.tupleRead(gcomm, oneObject), nprocsInt);
	}
}
