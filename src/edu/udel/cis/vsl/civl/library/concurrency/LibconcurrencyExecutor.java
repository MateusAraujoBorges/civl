package edu.udel.cis.vsl.civl.library.concurrency;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class LibconcurrencyExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library executor for concurrency.cvh.
	 * 
	 * @param name
	 *            The name of the library, which is concurrency.
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param modelFactory
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility to be used.
	 * @param civlConfig
	 *            The CIVL configuration configured by the user.
	 */
	public LibconcurrencyExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	/* ******************** Methods from BaseLibraryExecutor ******************* */

	/**
	 * Executes a system function call, updating the left hand side expression
	 * with the returned value if any.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param call
	 *            The function call statement to be executed.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
		// case "$barrier_create":
		// callEval = executeBarrierCreate(state, pid, process, arguments,
		// argumentValues, source);
		// break;
		// case "$barrier_enter":
		// callEval = executeBarrierEnter(state, pid, process, arguments,
		// argumentValues);
		// break;
		// case "$barrier_exit":
		// // does nothing
		// callEval = new Evaluation(state, null);
		// break;
		// case "$gbarrier_create":
		// callEval = executeGbarrierCreate(state, pid, process, arguments,
		// argumentValues, source);
		// break;
		// case "$barrier_destroy":
		// case "$gbarrier_destroy":
		// callEval = executeFree(state, pid, process, arguments,
		// argumentValues, source);
		// break;
		case "$gcollator_create":
			callEval = executeGcollectCheckerCreate(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$gcollator_destroy":
			callEval = executeGcollectCheckerDestroy(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$collator_create":
			callEval = executeCollectCheckerCreate(state, pid, process,
					arguments, argumentValues, source);
			break;
		case "$collator_destroy":
			callEval = this.executeFree(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$collator_check":
			callEval = executeCollectCheck(state, pid, process, arguments,
					argumentValues, source);
			break;
		default:
			throw new CIVLUnimplementedFeatureException("the function " + name
					+ " of library concurrency.cvh", source);
		}
		return callEval;
	}

	/* ************************** Private Methods ************************** */

	// TODO: Make the collective operation checking mechanism more general
	// instead just for MPI programs and stop reporting only MPI_ERRORs
	/**
	 * Executes the system function
	 * <code>$gcollect_checker $gcollect_checker_create($scope scope);</code>,
	 * it creates a <code>$gcollect_checker</code> object and returns a handle
	 * to that object.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The {@link String} identifier of the process
	 * @param lhs
	 *            The Left-hand side expression
	 * @param arguments
	 *            {@link Expression} of arguments of the function call
	 * @param argumentValues
	 *            {@link SymbolicExpression} of arguments of the function call
	 * @param source
	 *            {@link CIVLSource} of the function call statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeGcollectCheckerCreate(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		// incomplete $collect_record array
		SymbolicExpression imcompRecordsArray;
		SymbolicExpression gcollectChecker;
		CIVLType gcollectCheckerType;
		CIVLType collectRecordType;

		gcollectCheckerType = this.typeFactory
				.systemType(ModelConfiguration.GCOLLECT_CHECKER_TYPE);
		collectRecordType = this.typeFactory
				.systemType(ModelConfiguration.COLLECT_RECORD_TYPE);
		imcompRecordsArray = universe.emptyArray(collectRecordType
				.getDynamicType(universe));
		// make initial values of fields of gcollect_checker ready
		gcollectChecker = universe.tuple(
				(SymbolicTupleType) gcollectCheckerType
						.getDynamicType(universe), Arrays.asList(zero,
						imcompRecordsArray));
		return this.primaryExecutor.malloc(source, state, pid, process,
				arguments[0], scope, gcollectCheckerType, gcollectChecker);
	}

	/**
	 * Creates a local handle of a collective operations checker.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expression} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeCollectCheckerCreate(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gchecker = argumentValues[1];
		SymbolicExpression checker;
		CIVLType collectCheckerType;

		collectCheckerType = typeFactory
				.systemType(ModelConfiguration.COLLECT_CHECKER_TYPE);
		checker = universe
				.tuple((SymbolicTupleType) collectCheckerType
						.getDynamicType(universe), Arrays.asList(gchecker));
		return primaryExecutor.malloc(source, state, pid, process,
				arguments[0], scope, collectCheckerType, checker);
	}

	/**
	 * Destroy a global collective checker. The system function is suppose to
	 * return the number of junk records remaining the checker.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expression} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeGcollectCheckerDestroy(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gcheckerHandle = argumentValues[0];
		SymbolicExpression gchecker;
		NumericExpression records_length;
		Evaluation eval;

		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				arguments[0], gcheckerHandle, false, true);
		state = eval.state;
		gchecker = eval.value;
		records_length = (NumericExpression) universe.tupleRead(gchecker,
				zeroObject);
		state = this.executeFree(state, pid, process, arguments,
				argumentValues, source).state;
		return new Evaluation(state, records_length);
	}

	/**
	 * Execute the collective checking function:
	 * <code>_Bool $collect_check($collect_checker checker, int place, int nprocs,
	 *                           $bundle bundle)</code> This CIVL-C function
	 * returns false if and only if a process checks an existed record and get a
	 * mismatched result.<br>
	 * The execution logic is:<br>
	 * The first process for a record will create the record, and enqueue the
	 * record. <br>
	 * Rest processes marks themselves in the corresponding record. <br>
	 * The last marked process dequeue the record. <br>
	 * Since all records for processes must be checked in the same order, the
	 * logic makes sense.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String Identifier of the process
	 * @param lhs
	 *            The left-hand side expression of the statement
	 * @param arguments
	 *            The list of {@link Expression} of the arguments
	 * @param argumentValues
	 *            The list of {@link SymbolicExpression} of the arguments
	 * @param source
	 *            The CIVL source of the statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeCollectCheck(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression checkhandle = argumentValues[0];
		SymbolicExpression place = argumentValues[1];
		SymbolicExpression nprocs = argumentValues[2];
		SymbolicExpression bundledEntries = argumentValues[3];
		SymbolicExpression check, gcheckHandle, gcheck;
		SymbolicExpression records, tail_record;
		SymbolicExpression marksArray; // marks array of a record
		SymbolicExpression modifiedRecord = null;
		BooleanExpression markedElement; // element of a marks array
		BooleanExpression claim;
		NumericExpression records_length;
		NumericExpression numMarked; // number of marked processes in one record
		Reasoner reasoner;
		Evaluation eval;
		ResultType resultType;
		// fields indices
		IntObject marksArrayIdx = universe.intObject(1);
		IntObject numMarksIdx = universe.intObject(2);

		// Decides "numTypes", it must be a concrete number.
		reasoner = universe.reasoner(state.getPathCondition());
		eval = evaluator.dereference(source, state, process, arguments[0],
				checkhandle, false, true);
		state = eval.state;
		check = eval.value;
		gcheckHandle = universe.tupleRead(check, zeroObject);
		eval = evaluator.dereference(source, state, process, null,
				gcheckHandle, false, true);
		state = eval.state;
		gcheck = eval.value;
		// ------Step 1: Check if the process is the first process for a new
		// record
		records_length = (NumericExpression) universe.tupleRead(gcheck,
				zeroObject);
		claim = universe.equals(records_length, zero);
		resultType = reasoner.valid(claim).getResultType();
		records = universe.tupleRead(gcheck, oneObject);
		if (!resultType.equals(ResultType.YES)) {
			tail_record = universe.arrayRead(records,
					universe.subtract(records_length, one));
			marksArray = universe.tupleRead(tail_record, marksArrayIdx);
			markedElement = (BooleanExpression) universe.arrayRead(marksArray,
					(NumericExpression) place);
			resultType = reasoner.valid(markedElement).getResultType();
		}
		// ------Step 2.1: If the process is the first one for a record, create
		// a new record and enqueue it.
		// ------Step 2.2: If the process is not the first one for a record,
		// check if the record is matched with the existed one in queue and mark
		// itself.
		if (resultType.equals(ResultType.YES)) {
			SymbolicExpression newRecord = this.createANewRecord(state, place,
					nprocs, bundledEntries);

			records = universe.append(records, newRecord);
			records_length = universe.add(records_length, one);
			modifiedRecord = newRecord;
		} else {// TODO what if there are more than one records in the record
				// queue?
			SymbolicExpression unmarked_record = null;
			NumericExpression loopIdf = zero; // symbolic loop identifier
			boolean isMarked = true;
			SymbolicExpression marked_record;

			while (isMarked) {
				unmarked_record = universe.arrayRead(records, loopIdf);
				marksArray = universe.tupleRead(unmarked_record, marksArrayIdx);
				markedElement = (BooleanExpression) universe.arrayRead(
						marksArray, (NumericExpression) place);
				if (reasoner.valid(markedElement).getResultType()
						.equals(ResultType.NO))
					isMarked = false;
				else
					loopIdf = universe.add(loopIdf, one);
			}
			// No matter whether checking passed or not, the process always mark
			// itself so that the execution can continue
			marksArray = universe.tupleRead(unmarked_record, marksArrayIdx);
			marksArray = universe.arrayWrite(marksArray,
					(NumericExpression) place, trueValue);
			numMarked = (NumericExpression) universe.tupleRead(unmarked_record,
					numMarksIdx);
			numMarked = universe.add(numMarked, one);
			marked_record = universe.tupleWrite(unmarked_record, marksArrayIdx,
					marksArray);
			marked_record = universe.tupleWrite(marked_record, numMarksIdx,
					numMarked);
			records = universe.arrayWrite(records, loopIdf, marked_record);
			modifiedRecord = marked_record;
		}
		// ------Step 3: check if the process is the last one marks the record,
		// if it is, dequeue the record.
		numMarked = (NumericExpression) universe.tupleRead(modifiedRecord,
				numMarksIdx);
		claim = universe.equals(numMarked, nprocs);
		resultType = reasoner.valid(claim).getResultType();
		assert !resultType.equals(ResultType.MAYBE) : "Number of marked processes in record should be concrete.";
		if (resultType.equals(ResultType.YES)) {
			records = universe.removeElementAt(records, 0);
			records_length = universe.subtract(records_length, one);
		}
		gcheck = universe.tupleWrite(gcheck, this.zeroObject, records_length);
		gcheck = universe.tupleWrite(gcheck, oneObject, records);
		state = primaryExecutor.assign(source, state, pid, gcheckHandle,
				gcheck);
		return new Evaluation(state, universe.tupleRead(modifiedRecord,
				this.zeroObject));
	}

	/**
	 * Creates a new record of collective checking mechanism
	 * 
	 * @param state
	 *            The current state
	 * @param place
	 *            The place of the process in the collective checking system
	 * @param nprocs
	 *            The number of processes in the collective checking system
	 * @param bundle
	 *            The $bundle type object stores entries which should be stored
	 *            in a record.
	 * @return A new record of a collective operation checking system.
	 */
	private SymbolicExpression createANewRecord(State state,
			SymbolicExpression place, SymbolicExpression nprocs,
			SymbolicExpression bundle) {
		SymbolicExpression newRecord;
		SymbolicExpression newMarks;
		List<SymbolicExpression> newRecordComponents = new LinkedList<>();
		CIVLType collectRecordType = typeFactory
				.systemType(ModelConfiguration.COLLECT_RECORD_TYPE);

		newMarks = symbolicUtil.newArray(state.getPathCondition(),
				universe.booleanType(), (NumericExpression) nprocs,
				this.falseValue);
		newMarks = universe.arrayWrite(newMarks, (NumericExpression) place,
				this.trueValue);
		newRecordComponents.add(bundle);
		newRecordComponents.add(newMarks);
		newRecordComponents.add(one);
		newRecord = universe.tuple(
				(SymbolicTupleType) collectRecordType.getDynamicType(universe),
				newRecordComponents);
		return newRecord;
	}
}
