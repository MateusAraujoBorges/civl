package edu.udel.cis.vsl.civl.library.bundle;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

/**
 * <p>
 * Specification for bundle operations:<br>
 * The specification of bundle pack/unpack is essentially the specification of
 * get/set data from input/output arguments. Since CIVL implements multiple
 * dimensional arrays as nested arrays, assigning a set of data to a multiple
 * dimensional array will possibly involve several parts of different sub-arrays
 * inside a nested array. So the following description will note some
 * explanation of general cases for this get/set input/output arguments problem
 * which is totally irrelevant to bundle pack/unpack.
 * </p>
 * 
 * 
 * $bundle $bundle_pack(void *ptr, int size):<br>
 * <p>
 * Putting the whole or part of the object pointed by the first argument into
 * returned a bundle object.<br>
 * the first argument "ptr" is a pointer to the object part of which is going to
 * be assigned to the returned bundle type object. The second argument specifies
 * the size of the object pointed by the first argument. Here size means the
 * size of the data type times the the number of the elements of such data type
 * which are consisted of the data object will be packed in bundle.<br>
 * Note: For general cases, if some input argument, which happens to be a
 * pointer, has a specified data type, it's unnecessary to give the size unless
 * the function is just expecting part of the object pointed.
 * </p>
 * 
 * void $bundle_unpack($bundle bundle, void *ptr):
 * <p>
 * Extracting the whole data from a given bundle and assigning it to another
 * object pointed by the second argument. The pre-condition is the receiving
 * object must be able to contain the whole data object.<br>
 * The first argument is the bundle object which will be extracted. The second
 * argument is a pointer to receiving object. The pre-condition mentioned above
 * is defined as: If the receiving object has a compatible data type of itself
 * or elements of it with the data itself or elements of the data inside the
 * bundle and the size of the object (sometime it's just part of the object
 * because of different positions pointed by the pointer) is greater than or
 * equal to data in bundle, it's able to contain the whole data object. <br>
 * Note: For general setting output arguments cases, this precondition should
 * also hold. The only thing different is the data in bundle here can be data
 * from anywhere(Obviously general cases are irrelevant with bundle stuff).<br>
 * </p>
 * 
 * 
 */

public class LibbundleExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {

	/* **************************** Constructors *************************** */

	public LibbundleExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	/*
	 * ******************** Methods from BaseLibraryExecutor *******************
	 */

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$bundle_pack" :
				callEval = executeBundlePack(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$bundle_size" :
				callEval = executeBundleSize(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$bundle_unpack" :
				callEval = executeBundleUnpack(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$bundle_unpack_apply" :
				callEval = executeBundleUnpackApply(state, pid, process,
						arguments, argumentValues, source);
				break;
		}
		return callEval;
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Returns the size of a bundle.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param civlSource
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeBundleSize(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource civlSource) throws UnsatisfiablePathConditionException {
		SymbolicObject arrayObject;
		SymbolicExpression array;
		NumericExpression size;
		CIVLType baseType = typeFactory.bundleType().getStaticElementType(
				((IntObject) argumentValues[0].argument(0)).getInt());

		assert arguments.length == 1;
		assert argumentValues[0].operator() == SymbolicOperator.UNION_INJECT;
		arrayObject = argumentValues[0].argument(1);
		assert arrayObject instanceof SymbolicExpression;
		array = (SymbolicExpression) arrayObject;
		size = symbolicUtil.sizeof(civlSource,
				typeFactory.incompleteArrayType(baseType), array.type());
		return new Evaluation(state, size);
	}

	/**
	 * Creates a bundle from the memory region specified by ptr and size,
	 * copying the data into the new bundle:
	 * 
	 * <code>$bundle $bundle_pack(void *ptr, int size);</code>
	 * 
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * <code>void $bundle_unpack($bundle bundle, void *ptr, int size);</code>
	 * 
	 * Pre-Condition : The size of the object pointed by the given address
	 * should larger than or equal to the other parameter "size".<br>
	 * Post-Condition: The data in bundle is in the form of an unrolled one
	 * dimensional array.<br>
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param process
	 *            The information of the process.
	 * @param bundleType
	 *            The bundle type of the model.
	 * @param lhs
	 *            The left hand side expression of the call, which is to be
	 *            assigned with the returned value of the function call. If NULL
	 *            then no assignment happens.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeBundlePack(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression size = (NumericExpression) argumentValues[1];
		SymbolicUnionType symbolicBundleType;
		SymbolicExpression bundleContent = null;
		SymbolicExpression bundle = null;
		IntObject elementTypeIndexObj;
		Evaluation eval;
		int elementTypeIndex;
		CIVLBundleType bundleType = this.typeFactory.bundleType();
		BooleanExpression isPtrValid, isSizeGTZ;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		// requires : pointer is valid:
		isPtrValid = symbolicAnalyzer.isDerefablePointer(state, pointer).left;
		// requires : size > 0:
		isSizeGTZ = universe.lessThan(zero, size);
		if (isPtrValid.isFalse() || reasoner.valid(isPtrValid)
				.getResultType() != ResultType.YES) {
			errorLogger.logSimpleError(arguments[0].getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.POINTER,
					"Attempt to read/write a invalid pointer type variable.");
			throw new UnsatisfiablePathConditionException();
		}
		if (isSizeGTZ.isFalse() || reasoner.valid(isSizeGTZ)
				.getResultType() != ResultType.YES) {
			errorLogger.logSimpleError(arguments[1].getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"Attempt to pack data of 0 size.");
			throw new UnsatisfiablePathConditionException();
		}
		// test:
		Pair<SymbolicExpression, NumericExpression> ptr_count = pointerTyping(
				state, pid, pointer, size, source);
		CIVLType baseType = symbolicAnalyzer.typeOfObjByPointer(source, state,
				ptr_count.left);
		TypeEvaluation teval = evaluator.getDynamicType(state, pid, baseType,
				source, false);

		eval = getDataFrom(teval.state, pid, process, arguments[0],
				ptr_count.left, ptr_count.right, true, false,
				arguments[0].getSource());
		state = eval.state;
		bundleContent = eval.value;
		assert (bundleContent != null
				&& bundleContent.type().typeKind() == SymbolicTypeKind.ARRAY);

		SymbolicType bundleContentElementType = ((SymbolicArrayType) bundleContent
				.type()).elementType();

		// Packing bundle:
		symbolicBundleType = bundleType.getDynamicType(universe);
		elementTypeIndex = bundleType
				.getIndexOf(universe.pureType(bundleContentElementType));
		elementTypeIndexObj = universe.intObject(elementTypeIndex);
		bundle = universe.unionInject(symbolicBundleType, elementTypeIndexObj,
				bundleContent);
		return new Evaluation(state, bundle);
	}

	/**
	 * Copies the data out of the bundle into the region specified:
	 * 
	 * void $bundle_unpack($bundle bundle, void *ptr); <br>
	 * 
	 * Pre-Condition : The data in bundle is in the form of an falttened one
	 * dimensional array.<br>
	 * 
	 * @see{executeBunldePack :post-condition.<br>
	 * 
	 * 
	 * @author Ziqing Luo
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeBundleUnpack(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0];
		SymbolicExpression pointer = argumentValues[1];
		SymbolicExpression targetObject = null;
		SymbolicExpression bufPointer = null;
		Evaluation eval;
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;

		// checking if pointer is valid
		if (pointer.operator() != SymbolicOperator.TUPLE) {
			errorLogger.logSimpleError(arguments[1].getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.POINTER,
					"attempt to read/write an uninitialized variable by the pointer "
							+ pointer);
			throw new UnsatisfiablePathConditionException();
		}
		eval_and_pointer = this.bundleUnpack(state, pid, process,
				(SymbolicExpression) bundle.argument(1), arguments[0], pointer,
				source);
		eval = eval_and_pointer.left;
		// bufPointer is the pointer to targetObj which may be the ancestor
		// of the original pointer.
		bufPointer = eval_and_pointer.right;
		state = eval.state;
		// targetObject is the object will be assigned to the output
		// argument.
		targetObject = eval.value;
		// If it's assigned to an array or an object
		if (bufPointer != null && targetObject != null)
			state = primaryExecutor.assign(source, state, process, bufPointer,
					targetObject);
		else
			throw new CIVLInternalException(
					"Cannot complete unpack.\nAssigned pointer: " + bufPointer
							+ "\nAssigning object: " + targetObject,
					source);

		return new Evaluation(state, null);
	}

	/**
	 * bundle unpack then do an operation. This method corresponding to the
	 * CIVL-C function:
	 * <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * Bundle contains the first operand which is going to be used in the
	 * operation. The pointer "buf" points to the object stores the second
	 * operand which is going to be used in the operation.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param pid
	 *            The pid of the process
	 * @param process
	 *            The identifier of the process
	 * @param arguments
	 *            The expression of arguments of the CIVL-C function
	 *            <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * @param argumentValues
	 *            The symbolic expression of arguments of the CIVL-C function
	 *            <code>$bundle_unpack_apply($bundle bundle, void * buf, int count, $operation op);</code>
	 * @param source
	 *            The civl source of this statement
	 * @return the state after execution.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeBundleUnpackApply(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression bundle = argumentValues[0],
				pointer = argumentValues[1];
		SymbolicExpression assignedPtr;
		NumericExpression count = (NumericExpression) argumentValues[2],
				totalUnits;
		// Enumerator number of the operation
		NumericExpression operation = (NumericExpression) argumentValues[3];
		CIVLOperator CIVL_Op;
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;
		SymbolicExpression[] operands = new SymbolicExpression[2];
		SymbolicType operandElementType;
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);
		Evaluation eval = null;
		int countStep;
		// TODO: support struct operands, i.e. struct in bundle and buf ->
		// struct
		// Checking if pointer is valid.
		if (pointer.operator() != SymbolicOperator.TUPLE) {
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.POINTER,
					"attempt to read/write an invalid pointer type variable");
			throw new UnsatisfiablePathConditionException();
		}
		// In executor, operation must be concrete.
		// Translate operation
		CIVL_Op = translateOperator(
				((IntegerNumber) reasoner.extractNumber(operation)).intValue());
		countStep = (CIVL_Op == CIVLOperator.CIVL_MINLOC
				|| CIVL_Op == CIVLOperator.CIVL_MAXLOC) ? 2 : 1;
		totalUnits = universe.multiply(count, universe.integer(countStep));
		eval = getDataFrom(state, pid, process, arguments[1], pointer,
				totalUnits, true, false, arguments[1].getSource());
		state = eval.state;
		operands[1] = eval.value;
		// Obtain data form bundle
		operands[0] = (SymbolicExpression) bundle.argument(1);
		// convert operand0 to array type if it is a single element
		if (operands[0].type().typeKind() != SymbolicTypeKind.ARRAY)
			operands[0] = universe.array(operands[0].type(),
					Arrays.asList(operands[0]));
		// type checking for two operands:
		operandElementType = ((SymbolicArrayType) operands[0].type())
				.elementType();
		if (!((SymbolicArrayType) operands[1].type()).elementType()
				.equals(operandElementType)) {
			int bundleTypeIdx = ((IntObject) bundle.argument(0)).getInt();
			CIVLPointerType bufPtrType = (CIVLPointerType) arguments[1]
					.getExpressionType();

			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"Operands of $bundle_unpack_apply has different types:"
							+ "data in bundle has type: "
							+ modelFactory.typeFactory().bundleType()
									.getElementType(bundleTypeIdx)
							+ "\n " + arguments[1]
							+ " points to objects of type: "
							+ bufPtrType.baseType());
			throw new UnsatisfiablePathConditionException();
		}
		eval.value = applyCIVLOperation(state, pid, process, operands, CIVL_Op,
				count, operandElementType, source);
		eval_and_pointer = setDataFrom(state, pid, process, arguments[1],
				pointer, totalUnits, eval.value, false, source);
		eval = eval_and_pointer.left;
		assignedPtr = eval_and_pointer.right;
		state = eval.state;
		state = primaryExecutor.assign(source, state, process, assignedPtr,
				eval.value);
		return new Evaluation(state, null);
	}

	/**
	 * Evaluating for bundle_unpack execution. This function returns the value
	 * of the object and the pointer to that object(the return type is a Pair).
	 * The reason that why this function need. <br>
	 * Note: Data in bundle is in the form of a unrolled one dimensional array.
	 * 
	 * Implementation details: First, it's guaranteed that the data in bundle is
	 * always in the form of a one dimensional array(also can be understood as a
	 * unrolled array or a sequence of data).<br>
	 * Second, inside this function, it contains a cast from the one dimensional
	 * array mentioned above to another type specified by the parameter
	 * "pointer". A correct CIVL program or C program should make sure that cast
	 * is legal, otherwise an error will be reported.<br>
	 * Third, the object used to store the data in bundle can have a larger size
	 * than the data itself.
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param bundle
	 *            The bundle type object
	 * @param pointer
	 *            The pointer to the address of the object which will be
	 *            assigned by bundle data
	 * @param civlsource
	 *            The CIVL Source of the bundle_unpack statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Pair<Evaluation, SymbolicExpression> bundleUnpack(State state, int pid,
			String process, SymbolicExpression bundleData,
			Expression pointerExpr, SymbolicExpression pointer,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		SymbolicExpression data = bundleData;
		NumericExpression dataSize;
		Evaluation eval;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;

		// Since bundle unpack is called by executeBundleUnpack, it has no need
		// to check pointer validation here.
		dataSize = universe.length(data);
		// If data size is zero, do nothing.
		if (reasoner.isValid(universe.equals(dataSize, zero))) {
			eval = evaluator.dereference(civlsource, state, process, null,
					pointer, false);
			return new Pair<Evaluation, SymbolicExpression>(eval, pointer);
		}
		// If data size larger than one, return an array and the corresponding
		// pointer.
		eval_and_pointer = this.setDataFrom(state, pid, process, pointerExpr,
				pointer, dataSize, data, false, civlsource);
		return eval_and_pointer;
	}
}
