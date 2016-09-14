package edu.udel.cis.vsl.civl.library.mpi;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.MPIContractExpression.MPI_CONTRACT_EXPRESSION_KIND;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
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
	public final static String mpiExtentName = "_uf_$mpi_extent";

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
			case 1 : // character
			case 2 : // byte
				primitiveType = typeFactory.charType();
				break;
			case 3 : // short
			case 4 : // int
			case 5 : // long
			case 6 : // long long int
			case 7 : // unsigned long long
			case 8 : // long long
				primitiveType = typeFactory.integerType();
				break;
			case 9 : // float
			case 10 : // double
			case 11 : // long double
				primitiveType = typeFactory.realType();
				break;
			case 12 : // 2int
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
			case MPI_AGREE :
				return evaluateMPIAgreeExpression(state, pid, process,
						expression);
			case MPI_EQUALS :
				return evaluateMPIEquals(state, pid, process, expression);
			case MPI_EXTENT :
				return evaluateMPIExtent(state, pid, process, expression);
			case MPI_OFFSET :
				return evaluateMPIOffset(state, pid, process, expression);
			case MPI_REGION :
				return evaluateMPIRegion(state, pid, process, expression);
			case MPI_VALID :
				return evaluateMPIValid(state, pid, process, expression);
			default :
				throw new CIVLInternalException("Unreachable",
						expression.getSource());
		}
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
		Expression ptrExpr = expression.arguments()[0];
		Expression countExpr = expression.arguments()[1];
		Expression datatypeExpr = expression.arguments()[2];
		SymbolicExpression buf;
		NumericExpression count, realCount, datatype;
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, ptrExpr);
		state = eval.state;
		buf = eval.value;
		eval = evaluator.evaluate(state, pid, countExpr);
		state = eval.state;
		count = (NumericExpression) eval.value;
		eval = evaluator.evaluate(state, pid, datatypeExpr);
		state = eval.state;
		datatype = (NumericExpression) eval.value;

		Pair<SymbolicExpression, NumericExpression> mpiPtr_datatypeSize;
		SymbolicExpression mpiPtr;

		mpiPtr_datatypeSize = processMPIPointer(state, pid, process, ptrExpr,
				buf, datatypeExpr, datatype, expression.getSource());
		realCount = universe.multiply(count, mpiPtr_datatypeSize.right);
		mpiPtr = mpiPtr_datatypeSize.left;
		eval = getDataFrom(state, pid, process, ptrExpr, mpiPtr, realCount,
				false, false, expression.getSource());
		state = eval.state;
		// getDataFrom always return a sequence of objects (i.e. an array of
		// objects), but here if the count is equal to one, the receiver is
		// expecting a single object:
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		if (reasoner.isValid(universe.equals(one, universe.length(eval.value))))
			eval.value = universe.arrayRead(eval.value, zero);
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
	private Evaluation evaluateMPIEquals(State state, int pid, String process,
			MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression values[] = new SymbolicExpression[4];
		SymbolicExpression ptr0, ptr1;
		NumericExpression count, mpiDatatype;
		Evaluation eval;
		SymbolicExpression data0, data1;
		BooleanExpression result;
		Pair<SymbolicExpression, NumericExpression> mpiPtr_datatypeSize0,
				mpiPtr_datatypeSize1;

		// \mpi_equals() takes 4 arguments: pointer0, count, datatype, pointer1:
		for (int i = 0; i < 4; i++) {
			eval = evaluator.evaluate(state, pid, expression.arguments()[i]);
			state = eval.state;
			values[i] = eval.value;
		}
		count = (NumericExpression) values[1];
		mpiDatatype = (NumericExpression) values[2];
		mpiPtr_datatypeSize0 = processMPIPointer(state, pid, process,
				expression.arguments()[0], values[0], expression.arguments()[2],
				mpiDatatype, expression.getSource());
		mpiPtr_datatypeSize1 = processMPIPointer(state, pid, process,
				expression.arguments()[3], values[3], expression.arguments()[2],
				mpiDatatype, expression.getSource());
		ptr0 = mpiPtr_datatypeSize0.left;
		ptr1 = mpiPtr_datatypeSize1.left;

		NumericExpression realCount = universe.multiply(count,
				mpiPtr_datatypeSize0.right);

		eval = getDataFrom(state, pid, process, expression.arguments()[0], ptr0,
				realCount, false, false, expression.getSource());
		state = eval.state;
		data0 = eval.value;
		eval = getDataFrom(state, pid, process, expression.arguments()[3], ptr1,
				realCount, false, false, expression.getSource());
		state = eval.state;
		data1 = eval.value;
		result = universe.equals(data0, data1);
		eval.value = result;
		return eval;
	}

	/**
	 * <p>
	 * An MPI_Valid expression will evaluates to true if and only if the given
	 * pointer points to a sequence of objects that satisfiy the given type
	 * signiture.
	 * </p>
	 * 
	 * @param state
	 *            The program state when this expression evaluates
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the calling process
	 * @param expression
	 *            The {@link MPIContractExpression} which represents an
	 *            MPI_Valid expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIValid(State state, int pid, String process,
			MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression ptrExpr = expression.arguments()[0];
		Expression countExpr = expression.arguments()[1];
		Expression datatypeExpr = expression.arguments()[2];
		SymbolicExpression ptr;
		NumericExpression count, datatype, realOffset;
		BooleanExpression result;
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, ptrExpr);
		state = eval.state;
		ptr = eval.value;
		eval = evaluator.evaluate(state, pid, countExpr);
		state = eval.state;
		count = (NumericExpression) eval.value;
		eval = evaluator.evaluate(state, pid, datatypeExpr);
		state = eval.state;
		datatype = (NumericExpression) eval.value;

		// Currently the valid checking is done by this:
		// 1. The object type pointed by the given pointer must be consistent
		// with the given datatype;
		// 2. The given pointer is dereferable;
		// 3. The given pointer added with (count * \mpi_extent(datatype)) is
		// dereferable.
		Pair<SymbolicExpression, NumericExpression> mpiPtr_datatypeSize;

		mpiPtr_datatypeSize = processMPIPointer(state, pid, process, ptrExpr,
				ptr, datatypeExpr, datatype, expression.getSource());
		// ptr + (real_count - 1):
		realOffset = universe.subtract(
				universe.multiply(count, mpiPtr_datatypeSize.right), one);
		eval = evaluator.evaluatePointerAdd(state, process,
				mpiPtr_datatypeSize.left, realOffset, false,
				expression.getSource()).left;
		state = eval.state;
		result = symbolicAnalyzer.isDerefablePointer(state,
				mpiPtr_datatypeSize.left).left;
		result = universe.and(result,
				symbolicAnalyzer.isDerefablePointer(state, eval.value).left);
		eval.value = result;
		return eval;
	}

	/**
	 * <p>
	 * An MPI_Extent(datatype) expression will evaluates to the size of an given
	 * MPI_Datatype in number of bytes.
	 * </p>
	 * 
	 * @param state
	 *            The program state when this expression evaluates
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the calling process
	 * @param expression
	 *            The {@link MPIContractExpression} which represents an
	 *            MPI_Extent expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIExtent(State state, int pid, String process,
			MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression datatypeExpr = expression.arguments()[0];
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, datatypeExpr);
		state = eval.state;
		return eval;
	}

	/**
	 * <p>
	 * The MPI_Offset(ptr, count, datatype) expression semantically menas:
	 * <code> (char *)ptr + count * \mpi_extent(datatype) </code>
	 * </p>
	 * 
	 * @param state
	 *            The program state when this expression evaluates
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the calling process
	 * @param expression
	 *            The {@link MPIContractExpression} which represents an
	 *            MPI_Offset expression.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation evaluateMPIOffset(State state, int pid, String process,
			MPIContractExpression expression)
			throws UnsatisfiablePathConditionException {
		Expression ptrExpr = expression.arguments()[0];
		Expression countExpr = expression.arguments()[1];
		Expression datatypeExpr = expression.arguments()[2];
		SymbolicExpression ptr;
		NumericExpression count, datatype;
		Evaluation eval;

		eval = evaluator.evaluate(state, pid, ptrExpr);
		state = eval.state;
		ptr = eval.value;
		eval = evaluator.evaluate(state, pid, countExpr);
		state = eval.state;
		count = (NumericExpression) eval.value;
		eval = evaluator.evaluate(state, pid, datatypeExpr);
		state = eval.state;
		datatype = (NumericExpression) eval.value;

		Pair<SymbolicExpression, NumericExpression> mpiPtr_datatypeSize;

		mpiPtr_datatypeSize = processMPIPointer(state, pid, process, ptrExpr,
				ptr, datatypeExpr, datatype, expression.getSource());
		return evaluator.evaluatePointerAdd(state, process,
				mpiPtr_datatypeSize.left,
				universe.multiply(count, mpiPtr_datatypeSize.right), false,
				expression.getSource()).left;
	}

	/**
	 * <p>
	 * Checks if the type of the leaf node pointed by the given pointer 'ptr' on
	 * the pointed object is consistnt with the given MPI_Datatype
	 * 'mpiDatatype'.
	 * 
	 * Returns a pair of objects:
	 * <ul>
	 * <li><b>left</b>A new pointer which is obtained by replace the reference
	 * expression of the given pointer with a new reference to the leaf node of
	 * the pointed object. (e.g. int a[0]; &a is casted to &a[0])</li>
	 * <li><b>right</b>The number of primitive types which compose the given
	 * MPI_Datatype. (e.g. MPI_2INT is composed of 2 primitive types)</li>
	 * </ul>
	 * </p>
	 * 
	 * @param state
	 *            The program state when this method is called
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the process
	 * @param ptrExpr
	 *            The {@link Expression} of the given pointer
	 * @param ptr
	 *            The value of the given pointer
	 * @param mpiDatatypeExpr
	 *            The {@link Expression} of MPI_Datatype
	 * @param mpiDatatype
	 *            The value of the MPI_Datatype.
	 * @return a pair of objects:
	 *         <ul>
	 *         <li><b>left</b>A new pointer which is obtained by replace the
	 *         reference expression of the given pointer with a new reference to
	 *         the leaf node of the pointed object. (e.g. int a[0]; &a is casted
	 *         to &a[0])</li>
	 *         <li><b>right</b>The number of primitive types which compose the
	 *         given MPI_Datatype. (e.g. MPI_2INT is composed of 2 primitive
	 *         types)</li>
	 *         </ul>
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<SymbolicExpression, NumericExpression> processMPIPointer(
			State state, int pid, String process, Expression ptrExpr,
			SymbolicExpression ptr, Expression mpiDatatypeExpr,
			NumericExpression mpiDatatype, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		ReferenceExpression baseRef = symbolicAnalyzer
				.getLeafNodeReference(state, ptr, source);
		SymbolicExpression basePtr = symbolicUtil.makePointer(ptr, baseRef);
		CIVLType leafNodeType = symbolicAnalyzer.typeOfObjByPointer(source,
				state, basePtr);
		NumericExpression numPrimitives;
		Evaluation eval = evaluator.evaluateSizeofType(source, state, pid,
				leafNodeType);
		NumericExpression sizeof;
		BooleanExpression typeChecking;
		Reasoner reasoner;

		state = eval.state;
		sizeof = (NumericExpression) eval.value;
		// Now the "mpiDatatype" value is the sizeof(datatype) which encodes
		// SIZE_OF_TYPE symbols:
		numPrimitives = universe.divide(mpiDatatype, sizeof);
		// typeChecking = universe.divides(sizeof, mpiDatatype);
		// reasoner = universe.reasoner(state.getPathCondition());
		// if (!reasoner.isValid(typeChecking)) {
		// String ptrStr = symbolicAnalyzer.expressionEvaluation(state, pid,
		// ptrExpr, true).right;
		// String datatypeStr = symbolicAnalyzer.expressionEvaluation(state,
		// pid, mpiDatatypeExpr, true).right;
		//
		// errorLogger.logSimpleError(source, state, process,
		// symbolicAnalyzer.stateInformation(state),
		// ErrorKind.MPI_ERROR,
		// "Objects pointed by " + ptrStr
		// + " is inconsistent with the given MPI_Datatype: "
		// + datatypeStr);
		// }
		return new Pair<>(basePtr, numPrimitives);
	}
}
