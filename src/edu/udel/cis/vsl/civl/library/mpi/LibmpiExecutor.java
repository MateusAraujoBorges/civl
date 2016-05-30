package edu.udel.cis.vsl.civl.library.mpi;

import java.util.Arrays;
import java.util.Iterator;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.comm.LibcommEvaluator;
import edu.udel.cis.vsl.civl.library.comm.LibcommExecutor;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * <p>
 * This class represents a library executor for MPI libraries. This class is
 * responsible for processing following executions:
 * <ul>
 * <li><b>System functions defined in MPI libraries:</b>
 * <ul>
 * <li>$mpi_set_status</li>
 * <li>$mpi_get_status</li>
 * <li>$mpi_assert_consistent_base_type</li>
 * <li>$mpi_newGcomm</li>
 * <li>$mpi_getGcomm</li>
 * <li>$mpi_root_scope</li>
 * <li>$mpi_proc_scope</li>
 * <li>$mpi_p2pSendShot</li>
 * <li>$mpi_colSendShot</li>
 * <li>$mpi_p2pRecvShot</li>
 * <li>$mpi_colRecvShot</li>
 * </ul>
 * </li>
 * <li><b>Collective evaluation algorithm:</b>
 * {@link #executeCoassertWorker(State, int, String, Expression[], SymbolicExpression[], CIVLSource, boolean, ContractKind, Variable[])}
 * </li>
 * </ul>
 * </p>
 * 
 * @author ziqingluo
 * 
 */
public class LibmpiExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {
	private LibmpiEvaluator libEvaluator;

	public LibmpiExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		this.libEvaluator = new LibmpiEvaluator(name, evaluator, modelFactory,
				symbolicUtil, symbolicAnalyzer, civlConfig, libEvaluatorLoader);
	}

	/**
	 * <p>
	 * <b>Summary: </b> A public interface for using collective evaluation on a
	 * set of expressions.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param args
	 *            An array of arguments:{MPI communicator, expressions ... }
	 * @param argreedVars
	 *            An array of agreed variables. The value of them will be
	 *            delivered by the first process, rest of processes will assign
	 *            those values to their agreed variables
	 * @param kind
	 *            The kind of the snapshot entry
	 * @param source
	 *            The CIVLSource corresponding to the expressions
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public State executeCollectiveEvaluation(State state, int pid,
			String process, Expression[] args, Variable[] argreedVars,
			ContractKind kind, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues = new SymbolicExpression[1];
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, args[0]);
		state = eval.state;
		argumentValues[0] = eval.value;
		state = executeCoassertWorker(state, pid, process, args,
				argumentValues, source, true, kind, argreedVars).left;
		return state;
	}

	/* ************************* private methods **************************** */

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
		case "$mpi_set_status":
			callEval = executeSetStatus(state, pid, arguments, argumentValues);
			break;
		case "$mpi_get_status":
			callEval = executeGetStatus(state, pid);
			break;
		case "$mpi_check_buffer":
			callEval = executeMpiCheckBuffer(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$mpi_new_gcomm":
			callEval = executeNewGcomm(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$mpi_get_gcomm":
			callEval = executeGetGcomm(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$mpi_root_scope":
			callEval = executeRootScope(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$mpi_proc_scope":
			callEval = executeProcScope(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$mpi_p2pSendShot":
			callEval = executeSendShot(state, pid, process, functionName,
					arguments, argumentValues, zero, source);
			break;
		case "$mpi_colSendShot":
			callEval = executeSendShot(state, pid, process, functionName,
					arguments, argumentValues, one, source);
			break;
		case "$mpi_p2pRecvShot":
			callEval = executeRecvShot(state, pid, process, functionName,
					arguments, argumentValues, zero, source);
			break;
		case "$mpi_colRecvShot":
			callEval = executeRecvShot(state, pid, process, functionName,
					arguments, argumentValues, one, source);
			break;
		default:
			throw new CIVLInternalException("Unknown civl-mpi function: "
					+ name, source);
		}
		return callEval;
	}

	/**
	 * Executes system function
	 * <code>CMPI_Set_status($mpi_sys_status newStatus)</code>. Set the variable
	 * "_my_status" added by
	 * {@link edu.udel.cis.vsl.civl.transform.IF.MPI2CIVLTransformer} the given
	 * new value
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param call
	 *            the statement expression of the function call
	 * @param arguments
	 *            an array of expressions of arguments of the function
	 * @param argumentValues
	 *            an array of symbolic expressions of arguments of the function
	 * @return
	 */
	private Evaluation executeSetStatus(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues) {
		SymbolicExpression newStatus = argumentValues[0];
		Pair<Integer, Variable> myStatusVarInfo;
		State newState;

		myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
				"_mpi_process", "_mpi_status");
		newState = this.stateFactory.setVariable(state,
				myStatusVarInfo.right.vid(), myStatusVarInfo.left, newStatus);
		return new Evaluation(newState, null);
	}

	private Evaluation executeGetStatus(State state, int pid)
			throws UnsatisfiablePathConditionException {
		// variable (right in pair) and it's static scope
		Pair<Integer, Variable> myStatusVarInfo;
		SymbolicExpression valueOfMyStatusVar;
		// String process = state.getProcessState(pid).name() + "(id=" + pid +
		// ")";

		myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
				"_mpi_process", "_mpi_status");
		valueOfMyStatusVar = state.getDyscope(myStatusVarInfo.left).getValue(
				myStatusVarInfo.right.vid());
		return new Evaluation(state, valueOfMyStatusVar);
	}

	/**
	 * Search a variable with a scoping rule similar to dynamic scoping. Given a
	 * variable name and a function name, this method will search for each call
	 * stack entry e and all ancestors of e from the top stack entry e0, it
	 * looks for the first matched variable appears in the matched function
	 * scope.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param functionName
	 *            The name of the function
	 * @param varName
	 *            The name of the variable
	 * @return
	 */
	private Pair<Integer, Variable> getVariableWTDynamicScoping(State state,
			int pid, String functionName, String varName) {
		Iterator<? extends StackEntry> stackIter = state.getProcessState(pid)
				.getStackEntries().iterator();
		DynamicScope currDyscope = null;
		int currDyscopeId = -1;

		while (stackIter.hasNext()) {
			currDyscopeId = stackIter.next().scope();

			while (currDyscopeId > 0) {
				currDyscope = state.getDyscope(currDyscopeId);
				if (currDyscope.lexicalScope().containsVariable(varName))
					if (currDyscope.lexicalScope().function().name().name()
							.equals(functionName))
						return new Pair<>(currDyscopeId, currDyscope
								.lexicalScope().variable(varName));
				currDyscopeId = currDyscope.getParent();
			}
		}
		return new Pair<>(currDyscopeId, null);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Executing the function
	 * <code>$mpi_assert_consistent_base_type(void * ptr, MPI_Datatype datatype)</code>
	 * 
	 * This system function checks if the base type of an MPI_Datatype is
	 * consistent with the base type of the object pointed by the given pointer.
	 * 
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            {@link Expression}s of arguments of the system function
	 * @param argumentValues
	 *            {@link SymbolicExpression}s of arguments of the system
	 *            function
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeMpiCheckBuffer(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLSource ptrSource = arguments[0].getSource();
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression assertedType = (NumericExpression) argumentValues[2], primitiveTypeCount, count;
		CIVLType realType;
		SymbolicType realSymType, assertedSymType;
		Reasoner reasoner;
		IntegerNumber assertedTypeEnum;
		Pair<BooleanExpression, ResultType> checkPointer;
		Pair<CIVLPrimitiveType, NumericExpression> mpiType2Civl;
		Evaluation eval;

		count = (NumericExpression) argumentValues[1];
		reasoner = universe.reasoner(state.getPathCondition());
		if (reasoner.isValid(universe.equals(count, zero)) || pointer.isNull()) {
			return new Evaluation(state, null);
		}
		if (symbolicUtil.isNullPointer(pointer))
			return new Evaluation(state, null);
		// this assertion doesn't need recovery:
		if (!pointer.operator().equals(SymbolicOperator.TUPLE)) {
			errorLogger
					.logSimpleError(arguments[0].getSource(), state, process,
							this.symbolicAnalyzer.stateInformation(state),
							ErrorKind.POINTER,
							"attempt to read/write a non-concrete pointer type variable");
			return new Evaluation(state, null);
		}
		checkPointer = symbolicAnalyzer.isDerefablePointer(state, pointer);
		if (checkPointer.right != ResultType.YES) {
			state = errorLogger.logError(arguments[0].getSource(), state,
					process, this.symbolicAnalyzer.stateInformation(state),
					checkPointer.left, checkPointer.right, ErrorKind.POINTER,
					"attempt to read/write a invalid pointer type variable");
			// return state;
		}
		realType = symbolicAnalyzer.getArrayBaseType(state, ptrSource, pointer);
		realSymType = realType.getDynamicType(universe);
		assertedTypeEnum = (IntegerNumber) reasoner.extractNumber(assertedType);
		mpiType2Civl = mpiTypeToCIVLType(assertedTypeEnum.intValue(), source);
		assertedSymType = mpiType2Civl.left.getDynamicType(universe);
		primitiveTypeCount = mpiType2Civl.right;
		// assertion doesn't need recovery:
		if (!assertedSymType.equals(realSymType)) {
			errorLogger
					.logSimpleError(
							source,
							state,
							process,
							this.symbolicAnalyzer.stateInformation(state),
							ErrorKind.MPI_ERROR,
							"The primitive type "
									+ realType.toString()
									+ " of the object pointed by the input pointer argument ["
									+ ptrSource.getLocation()
									+ ":"
									+ arguments[0]
									+ "] of"
									+ " MPI routines is not consistent with the specified MPI_Datatype.");
		}
		eval = evaluator.dereference(source, state, process, arguments[0],
				pointer, false);
		state = eval.state;
		count = universe.multiply(primitiveTypeCount, count);
		// TODO: here needs be improved:
		if (reasoner.isValid(universe.equals(count, one)))
			return new Evaluation(state, null);
		try {
			libEvaluator.getDataFrom(state, process, arguments[0], pointer,
					count, false, ptrSource);
		} catch (UnsatisfiablePathConditionException e) {
			errorLogger
					.logSimpleError(
							source,
							state,
							process,
							symbolicAnalyzer.stateInformation(state),
							ErrorKind.MPI_ERROR,
							"The type of the object pointed by "
									+ arguments[0]
									+ " is inconsistent with the specified MPI datatype signiture.");
		}
		return new Evaluation(state, null);
	}

	/**
	 * add new CMPI_Gcomm to seq
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeNewGcomm(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mpiRootScope = argumentValues[0];
		SymbolicExpression newCMPIGcomm = argumentValues[1];
		int sid = modelFactory.getScopeId(arguments[0].getSource(),
				mpiRootScope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");
		SymbolicExpression gcomms;
		NumericExpression idx;

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		idx = universe.length(gcomms);
		gcomms = universe.append(gcomms, newCMPIGcomm);
		state = stateFactory.setVariable(state, gcommsVar.vid(), sid, gcomms);
		return new Evaluation(state, idx);
	}

	private Evaluation executeGetGcomm(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		NumericExpression index = (NumericExpression) argumentValues[1];
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gcomms, gcomm;
		int sid = modelFactory.getScopeId(arguments[0].getSource(), scope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		gcomm = universe.arrayRead(gcomms, index);
		return new Evaluation(state, gcomm);
	}

	private Evaluation executeRootScope(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression gcommHandle;
		SymbolicExpression scopeVal;
		Evaluation eval;
		int sid;

		eval = evaluator.dereference(source, state, process, arguments[0],
				commHandle, false);
		state = eval.state;
		gcommHandle = universe.tupleRead(eval.value, oneObject);
		sid = symbolicUtil.getDyscopeId(source, gcommHandle);
		scopeVal = modelFactory.scopeValue(sid);
		return new Evaluation(state, scopeVal);
	}

	private Evaluation executeProcScope(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression scopeVal;
		int sid;

		sid = symbolicUtil.getDyscopeId(source, commHandle);
		scopeVal = modelFactory.scopeValue(sid);
		return new Evaluation(state, scopeVal);
	}

	/**************************** Contract section ****************************/
	/**
	 * Execute $mpi_coassert(MPI_Comm, _Bool). The second argument shall not be
	 * evaluated at calling phase. It will be evaluated at some point following
	 * collective assertion semantics. See
	 * {@link #executeCoassertWorker(State, int, String, Expression[], SymbolicExpression[], CIVLSource, boolean)}
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            The Expression array of the arguments
	 * @param source
	 *            The CIVLSource of the function call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	@SuppressWarnings("unused")
	private Evaluation executeCoassertArrive(State state, int pid,
			String process, Expression[] arguments, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression[] argumentValues = new SymbolicExpression[1];
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, arguments[0]);
		state = eval.state;
		argumentValues[0] = eval.value;
		state = executeCoassertWorker(state, pid, process, arguments,
				argumentValues, source, false, null, null).left;
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * <b>Summary: </b> The generic core method for executing collective
	 * evaluation.
	 * </p>
	 * <p>
	 * <b>Details:</b> The main logic for collective evaluation algorithm is:
	 * For a set of locations L, each process will reach a location l in L
	 * exactly once. For all processes P, the first process p0 reaches its'
	 * corresponding l, creates a snapshot entry and saves it snapshot. Rest of
	 * processes P', P' = P - {p0}, just save their snapshots on the created
	 * snapshot entry. The last process pn, pn in P', is responsible for dequeue
	 * the entry.
	 * </p>
	 * 
	 * @param call
	 *            the function call statement
	 * @param state
	 *            the current state
	 * @param pid
	 *            the Process ID
	 * @param process
	 *            the String Identifier of the process
	 * @param arguments
	 *            The expression array of the arguments of the function
	 * @param argumentValues
	 *            The symbolic expression array of the argument of the function
	 * @param source
	 * @param isContract
	 *            flag controls whether an error will be reported as a contract
	 *            violation or assertion violation
	 * @param kind
	 *            {@link ContractClauseKind} if the the collective entry is
	 *            associated to a contract, if it is associated to a collective
	 *            assert, kind is null.
	 * @param agreedVars
	 *            Optional: An array of agreed variables. Values of agreed
	 *            variables will be delivered by the first process p0. Rest
	 *            processes assign their agreed variables with those delivered
	 *            values.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<State, Boolean> executeCoassertWorker(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source,
			boolean isContract, ContractKind kind, Variable[] agreedVars)
			throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		Expression MPICommExpr = arguments[0];
		Expression assertion = arguments[1];
		// Symbolic Expressions
		SymbolicExpression MPIComm = argumentValues[0];
		SymbolicExpression colCommHandle = universe.tupleRead(MPIComm,
				universe.intObject(LibmpiEvaluator.colCommField));
		NumericExpression symNprocs;
		NumericExpression symPlace;
		NumericExpression symQueueID = (NumericExpression) universe.tupleRead(
				MPIComm, universe.intObject(4));
		SymbolicExpression colGcomm, colGcommHandle, colComm;
		ImmutableCollectiveSnapshotsEntry[] queue;
		boolean createNewEntry;
		boolean entryComplete;
		IntegerNumber tmpNumber;
		int place, nprocs;
		int queueLength;
		int queueID;
		Evaluation eval;

		eval = evaluator.dereference(MPICommExpr.getSource(), tmpState,
				process, MPICommExpr, colCommHandle, false);
		tmpState = (ImmutableState) eval.state;
		colComm = eval.value;
		colGcommHandle = universe.tupleRead(colComm, oneObject);
		eval = evaluator.dereference(MPICommExpr.getSource(), tmpState,
				process, MPICommExpr, colGcommHandle, false);
		tmpState = (ImmutableState) eval.state;
		colGcomm = eval.value;
		// reads and makes following variables concrete:
		// place: another name for ranks of process in MPI communicator
		// nprocs: number of processes
		symPlace = (NumericExpression) universe.tupleRead(colComm, zeroObject);
		symNprocs = (NumericExpression) universe
				.tupleRead(colGcomm, zeroObject);
		tmpNumber = (IntegerNumber) universe.extractNumber(symPlace);
		assert tmpNumber != null : "The place of a process in MPI should be concrete.";
		place = tmpNumber.intValue();
		tmpNumber = (IntegerNumber) universe.extractNumber(symNprocs);
		assert tmpNumber != null : "The number of processes in MPI should be concrete.";
		nprocs = tmpNumber.intValue();
		tmpNumber = (IntegerNumber) universe.extractNumber(symQueueID);
		assert tmpNumber != null : "The index of CMPI_Gcomm should be concrete.";
		queueID = tmpNumber.intValue();
		// CASE ONE: find out the entry this process should mark, if no such
		// entry,
		// create one.
		createNewEntry = true; // if no corresponding entry there
		entryComplete = false; // if the entry is completed
		queue = stateFactory.getSnapshotsQueue(tmpState, queueID);
		if (queue != null) {
			queueLength = queue.length;
			for (int entryPos = 0; entryPos < queueLength; entryPos++) {
				ImmutableCollectiveSnapshotsEntry entry = queue[entryPos];

				if (!entry.isRecorded(place) && entry.contractKind() == kind) {
					createNewEntry = false;
					tmpState = stateFactory.addToCollectiveSnapshotsEntry(
							tmpState, pid, place, queueID, entryPos, assertion);
					// Pick up:
					if (kind == ContractKind.REQUIRES)
						tmpState = (ImmutableState) pickupAgreedVariables(
								tmpState, pid, entry);
					entryComplete = stateFactory.getSnapshotsQueue(tmpState,
							queueID)[0].isComplete();
					break;
				}
			}
		}
		// CASE TWO: if it needs a new entry, then create it
		if (createNewEntry) {
			SymbolicExpression channels = null;
			int agreedVarArray[][] = null;
			SymbolicExpression agreedValues[] = null;

			if (civlConfig.isEnableMpiContract()) {
				SymbolicExpression colChannel = universe
						.tupleRead(colGcomm, universe
								.intObject(LibcommEvaluator.messageBufferField));
				SymbolicExpression p2pChannel = this.getchannelsFromCommHandle(
						tmpState, pid, process, MPICommExpr,
						universe.tupleRead(MPIComm, universe
								.intObject(LibmpiEvaluator.p2pCommField)));

				channels = universe.array(colChannel.type(),
						Arrays.asList(p2pChannel, colChannel));
			}
			// Deliver agreed variables:
			if (agreedVars != null && kind == ContractKind.REQUIRES) {
				Pair<int[][], SymbolicExpression[]> agreedVarsVals = prepareDeliverAgreedVariables(
						tmpState, pid, agreedVars);

				agreedVarArray = agreedVarsVals.left;
				agreedValues = agreedVarsVals.right;
			}
			// change the corresponding CollectiveSnapshotsEntry
			tmpState = stateFactory.createCollectiveSnapshotsEnrty(tmpState,
					pid, nprocs, place, queueID, assertion, channels, kind,
					agreedVarArray, agreedValues);
			entryComplete = (1 == nprocs);
		}
		// CASE THREE: if the entry is completed ?
		if (entryComplete)
			return new Pair<>(dequeueCollectiveEntryAndEvaluation(tmpState,
					queueID, MPICommExpr, isContract), true);
		return new Pair<>(tmpState, false);
	}

	private Pair<CIVLPrimitiveType, NumericExpression> mpiTypeToCIVLType(
			int MPI_TYPE, CIVLSource source) {
		CIVLPrimitiveType primitiveType;
		NumericExpression count = one;

		switch (MPI_TYPE) {
		case 0: // char
			primitiveType = typeFactory.charType();
			break;
		case 1: // character
			primitiveType = typeFactory.charType();
			break;
		case 8: // int
			primitiveType = typeFactory.integerType();
			break;
		case 20: // long
			primitiveType = typeFactory.integerType();
			break;
		case 22: // float
			primitiveType = typeFactory.realType();
			break;
		case 23: // double
			primitiveType = typeFactory.realType();
			break;
		case 24: // long double
			primitiveType = typeFactory.realType();
			break;
		case 27: // long long
			primitiveType = typeFactory.integerType();
			break;
		case 39: // 2int
			primitiveType = typeFactory.integerType();
			count = two;
			break;
		default:
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

	/**
	 * Dequeues a complete collective entry and evaluates assertions of it.
	 * 
	 * @param state
	 *            The state that the collective entry just completes
	 * @param queueID
	 *            The ID associates to an MPI communicator, which is also used
	 *            to identify a collective queue.
	 * @param MPICommExpr
	 *            The expression of an MPI communicator
	 * @param isContrac
	 *            Flag indicates whether the evaluation is for a collective
	 *            contract or assert.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State dequeueCollectiveEntryAndEvaluation(State state, int queueID,
			Expression MPICommExpr, boolean isContract)
			throws UnsatisfiablePathConditionException {
		ImmutableCollectiveSnapshotsEntry entry;
		ImmutableState mergedState;

		entry = stateFactory.peekCollectiveSnapshotsEntry(state, queueID);
		mergedState = stateFactory.mergeMonostates(state, entry);
		collectiveEvaluation(mergedState, entry.getAllAssertions(),
				MPICommExpr, isContract);
		state = stateFactory.dequeueCollectiveSnapshotsEntry(state, queueID);
		return state;
	}

	/**
	 * Evaluating assertions for all processes participating a $mpi_coassert()
	 * (or a collective contract) function.
	 * 
	 * @param mergedState
	 *            The state on where the evaluation happens
	 * @param assertions
	 *            The list of assertions, one for each process
	 * @param pid
	 *            The PID of the process
	 * @param group
	 *            The expression of the group contains all participated
	 *            processes
	 * @param isContract
	 *            Flag indicate whether those assertions are coming from a
	 *            collective assert or a collective contract
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State collectiveEvaluation(State mergedState,
			Expression[] assertions, Expression group, boolean isContract)
			throws UnsatisfiablePathConditionException {
		String process;
		Evaluation eval;
		Reasoner reasoner;

		mergedState = stateFactory.simplify(mergedState);
		for (int place = 0; place < assertions.length; place++) {
			Expression snapShotAssertion = assertions[place];
			BooleanExpression assertionVal;
			ResultType resultType;
			String message;

			eval = evaluator.evaluate(mergedState, place, snapShotAssertion);
			mergedState = eval.state;
			assertionVal = (BooleanExpression) eval.value;
			reasoner = universe.reasoner(mergedState.getPathCondition());
			resultType = reasoner.valid(assertionVal).getResultType();
			if (!resultType.equals(ResultType.YES)) {
				Expression[] args = { snapShotAssertion };
				SymbolicExpression[] argVals = { assertionVal };

				// Contracts don't need recovery:
				if (isContract) {
					mergedState = this.primaryExecutor.reportContractViolation(
							mergedState, snapShotAssertion.getSource(), place,
							resultType, assertionVal, snapShotAssertion,
							ErrorKind.MPI_ERROR, group.toString());
				} else {
					message = " assertion:" + assertions[place];
					process = "process with rank: " + place
							+ " participating the " + "$mpi_coassert().";
					mergedState = this.reportAssertionFailure(mergedState,
							place, process, resultType,
							"$mpi_coassert violation: " + message, args,
							argVals, snapShotAssertion.getSource(),
							assertionVal, 1);
				}
			}
		}
		return mergedState;
	}

	private SymbolicExpression getchannelsFromCommHandle(State state, int pid,
			String process, Expression expr, SymbolicExpression commHandle)
			throws UnsatisfiablePathConditionException {
		Evaluation eval = evaluator.dereference(expr.getSource(), state,
				process, expr, commHandle, false);
		SymbolicExpression comm, gcomm, gcommHandle;

		comm = eval.value;
		gcommHandle = universe.tupleRead(comm,
				universe.intObject(LibcommEvaluator.gcommHandleInCommField));
		eval = evaluator.dereference(expr.getSource(), eval.state, process,
				expr, gcommHandle, false);
		gcomm = eval.value;
		return universe.tupleRead(gcomm,
				universe.intObject(LibcommEvaluator.messageBufferField));
	}

	/**
	 * * Executes the system functions
	 * <code>$system void $mpi_p2pSendShot(int commID, int source, int dest, int tag);</code>
	 * and
	 * <code>$system void $mpi_colSendShot(int commID, int source, int dest, int tag);</code>
	 * 
	 * <p>
	 * This method finds out the corresponding snapshots queue then do a message
	 * send on all unrecorded snapshot entries in that queue. Here an unrecorded
	 * snapshot entry is the entry that hasn't been reached by this process.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function name of the executed function, used for error
	 *            reporting
	 * @param arguments
	 *            Expression arrays of arguments.
	 * @param argumentValues
	 *            SymbolicExpression arrays of arguments
	 * @param channelIdx
	 *            The channel index. It shall be either zero or one which
	 *            denotes weather the modification happens on point-2-point
	 *            buffer or collective buffer
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeSendShot(State state, int pid, String process,
			String function, Expression[] arguments,
			SymbolicExpression[] argumentValues, NumericExpression channelIdx,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue;
		SymbolicExpression[] msgBuffers;
		int mpiCommIdInt, queueLength;

		// MPI_Comm ID should always be concrete:
		mpiCommIdInt = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[0]))
				.intValue();
		queue = stateFactory.getSnapshotsQueue(tmpState, mpiCommIdInt);
		if (queue != null && queue.length > 0) {
			// change entries in the queue
			queueLength = queue.length;
			msgBuffers = new SymbolicExpression[queueLength];
			for (int i = 0; i < queueLength; i++) {
				ImmutableCollectiveSnapshotsEntry entry = queue[i];
				SymbolicExpression twoBuffers;
				int place = ((IntegerNumber) universe
						.extractNumber((NumericExpression) argumentValues[2]))
						.intValue();

				twoBuffers = entry.getMsgBuffers();
				if (!entry.isRecorded(place)) {
					if (twoBuffers != null) {
						SymbolicExpression channel;

						channel = universe.arrayRead(twoBuffers, channelIdx);
						channel = doMPISendOnSnapshots(state, process,
								function, channel, argumentValues[1],
								civlsource);
						twoBuffers = universe.arrayWrite(twoBuffers,
								channelIdx, channel);
					}
				}
				msgBuffers[i] = twoBuffers;
			}
			state = stateFactory.commitUpdatedChannelsToEntries(tmpState,
					mpiCommIdInt, msgBuffers);
		}
		return new Evaluation(state, null);
	}

	/**
	 * Executes the system functions
	 * <code>$system void $mpi_p2pRecvShot(int commID, int source, int dest, int tag);</code>
	 * and
	 * <code>$system void $mpi_colRecvShot(int commID, int source, int dest, int tag);</code>
	 * 
	 * <p>
	 * This method finds out the corresponding snapshots queue then do a message
	 * receive on all unrecorded snapshot entries in that queue. Here an
	 * unrecorded snapshot entry is the entry that hasn't been reached by this
	 * process.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The function name of the executed function, used for error
	 *            reporting
	 * @param arguments
	 *            Expression arrays of arguments.
	 * @param argumentValues
	 *            SymbolicExpression arrays of arguments
	 * @param channelIdx
	 *            The channel index. It shall be either zero or one which
	 *            denotes weather the modification happens on point-2-point
	 *            buffer or collective buffer
	 * @param civlsource
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeRecvShot(State state, int pid, String process,
			String function, Expression[] arguments,
			SymbolicExpression[] argumentValues, NumericExpression channelIdx,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		ImmutableState tmpState = (ImmutableState) state;
		ImmutableCollectiveSnapshotsEntry[] queue;
		int mpiCommIdInt, queueLength;
		SymbolicExpression[] msgBuffers;
		NumericExpression src, dest, tag;
		// Flag: is there any entry in queue being modified.
		boolean anyEntryModified = false;
		int place;

		src = (NumericExpression) argumentValues[1];
		dest = (NumericExpression) argumentValues[2];
		tag = (NumericExpression) argumentValues[3];
		// MPI_Comm ID should always be concrete:
		mpiCommIdInt = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[0]))
				.intValue();
		queue = stateFactory.getSnapshotsQueue(tmpState, mpiCommIdInt);
		place = ((IntegerNumber) universe
				.extractNumber((NumericExpression) argumentValues[2]))
				.intValue();
		if (queue != null && queue.length > 0) {
			// change entries in the queue
			queueLength = queue.length;
			msgBuffers = new SymbolicExpression[queueLength];
			for (int i = 0; i < queueLength; i++) {
				SymbolicExpression twoMsgBuffers;
				ImmutableCollectiveSnapshotsEntry entry = queue[i];

				if (!entry.isRecorded(place)) {
					twoMsgBuffers = entry.getMsgBuffers();
					anyEntryModified = true;
					if (twoMsgBuffers != null) {
						SymbolicExpression msgBuffer = universe.arrayRead(
								twoMsgBuffers, channelIdx);

						msgBuffer = doMPIRecvOnSnapshots(tmpState, pid,
								process, function, msgBuffer, src, dest, tag,
								civlsource);
						twoMsgBuffers = universe.arrayWrite(twoMsgBuffers,
								channelIdx, msgBuffer);
						msgBuffers[i] = twoMsgBuffers;
					} else
						msgBuffers[i] = null;
				} else
					msgBuffers[i] = entry.getMsgBuffers();
			}
			if (anyEntryModified)
				state = stateFactory.commitUpdatedChannelsToEntries(tmpState,
						mpiCommIdInt, msgBuffers);
		}
		return new Evaluation(state, null);
	}

	/**
	 * Loads the "comm" library executor to do a message enqueue operation on
	 * the given message channel.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The name of the function
	 * @param channel
	 *            The Symbolic Expression of the message channel
	 * @param msg
	 *            The Symbolic Expression of the message
	 * @param civlsource
	 *            The {@link CIVLSource} of where in the source file causes this
	 *            execution
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression doMPISendOnSnapshots(State state,
			String process, String function, SymbolicExpression channel,
			SymbolicExpression msg, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		LibcommExecutor libexecutor;

		try {
			libexecutor = (LibcommExecutor) libExecutorLoader
					.getLibraryExecutor("comm", primaryExecutor, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			return libexecutor.putMsgInChannel(channel, msg, civlsource);
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library executor for the library"
					+ " comm for the function " + function);
			errorLogger.logSimpleError(civlsource, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * Loads the "comm" library executor to do a message dequeue operation on
	 * the given message channel.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param function
	 *            The name of the function
	 * @param channel
	 *            The Symbolic Expression of the message channel
	 * @param src
	 *            The Symbolic Expression of the source of the message
	 * @param dest
	 *            The Symbolic Expression of the destination of the message
	 * @param tag
	 *            The Symbolic Expression of the message tag
	 * @param civlsource
	 *            The {@link CIVLSource} of where the source file causes this
	 *            execution.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private SymbolicExpression doMPIRecvOnSnapshots(State state, int pid,
			String process, String function, SymbolicExpression channel,
			NumericExpression src, NumericExpression dest,
			NumericExpression tag, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException {
		LibcommExecutor libexecutor;

		try {
			libexecutor = (LibcommExecutor) libExecutorLoader
					.getLibraryExecutor("comm", primaryExecutor, modelFactory,
							symbolicUtil, symbolicAnalyzer);
			return libexecutor.getMsgOutofChannel(state, pid, process, channel,
					src, dest, tag, civlsource).right;
		} catch (LibraryLoaderException e) {
			StringBuffer message = new StringBuffer();

			message.append("unable to load the library executor for the library comm"
					+ " for the function " + function);
			errorLogger.logSimpleError(civlsource, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.LIBRARY, message.toString());
			throw new UnsatisfiablePathConditionException();
		}
	}

	/**
	 * <p>
	 * <b>Summary: </b> Helper method. Transform an array of variables to two
	 * arrays:
	 * <ul>
	 * <li>variable ID array: int[][2]: Each variable is represented by a VID
	 * and a lexical scope ID;</li>
	 * <li>value array: SymbolicExpression[] : values for given variables.</li>
	 * </ul>
	 * 
	 * This the form that what a {@link CollectiveSnapshotsEntry} takes for
	 * agreed variables.
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param agreedVars
	 *            An array of {@link Variable}.
	 * @return A {@link Pair} of a variable set and its value set.
	 */
	private Pair<int[][], SymbolicExpression[]> prepareDeliverAgreedVariables(
			State state, int pid, Variable[] agreedVars) {
		int agreedVarArray[][] = new int[agreedVars.length][2];
		SymbolicExpression agreedValues[] = new SymbolicExpression[agreedVars.length];

		for (int i = 0; i < agreedVars.length; i++) {
			agreedVarArray[i][0] = agreedVars[i].vid();
			agreedVarArray[i][1] = agreedVars[i].scope().id();
			agreedValues[i] = state.valueOf(pid, agreedVars[i]);
		}
		return new Pair<>(agreedVarArray, agreedValues);
	}

	/**
	 * <p>
	 * <b>Summary: </b>Helper method, assigns corresponding variables with a
	 * given set of agreed variables V and their values Val. V and Val are save
	 * in a {@link CollectiveSnapshotsEntry}
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the current process
	 * @param entry
	 *            The {@linkCollectiveSnapshotsEntry} contains a set of agreed
	 *            variables that should be assigned.
	 * @return The state after all assignments
	 */
	private State pickupAgreedVariables(State state, int pid,
			CollectiveSnapshotsEntry entry) {
		Iterator<Pair<int[], SymbolicExpression>> agreedVarsIter = entry
				.agreedValueIterator();

		while (agreedVarsIter.hasNext()) {
			Pair<int[], SymbolicExpression> agreedValues = agreedVarsIter
					.next();

			int dyscopeId = state.getDyscope(pid, agreedValues.left[1]);
			state = stateFactory.setVariable(state, agreedValues.left[0],
					dyscopeId, agreedValues.right);
		}
		return state;
	}
}
