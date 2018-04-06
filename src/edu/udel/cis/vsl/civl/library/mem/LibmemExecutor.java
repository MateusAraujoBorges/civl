package edu.udel.cis.vsl.civl.library.mem;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;
import java.util.function.Function;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.DynamicWriteSet;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.library.mem.WriteSetOperations.AssignableRefreshment;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;

public class LibmemExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {

	private Evaluator errSideEffectFreeEvaluator;

	private WriteSetRefresher wsRefresher = null;

	private WriteSetWidenOperator wsWideningOperator = null;

	private WriteSetUnionOperator wsUnionOperator = null;

	private WriteSetGroupOperator wsGroupOperator = null;

	public LibmemExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);

		Function<SymbolicExpression, IntegerNumber> scopeValueToKey = typeFactory
				.scopeType().scopeValueToIdentityOperator(universe);

		this.wsRefresher = WriteSetOperations.dynamicWriteSetRefresher(universe,
				symbolicUtil);
		this.wsWideningOperator = WriteSetOperations.widenOperator(universe,
				symbolicUtil);
		this.wsUnionOperator = WriteSetOperations.unionOperator(universe,
				symbolicUtil);
		this.wsGroupOperator = WriteSetOperations.groupOperator(universe,
				symbolicUtil, scopeValueToKey);
		this.errSideEffectFreeEvaluator = Semantics
				.newErrorSideEffectFreeEvaluator(modelFactory, stateFactory,
						libEvaluatorLoader, libExecutorLoader, symbolicUtil,
						symbolicAnalyzer, stateFactory.memUnitFactory(),
						errorLogger, civlConfig);
	}

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$write_set_push" :
				callEval = executeWriteSetPush(state, pid, arguments,
						argumentValues, source);
				break;
			case "$write_set_pop" :
				callEval = executeWriteSetPop(state, pid, arguments,
						argumentValues, source);
				break;
			case "$write_set_peek" :
				callEval = executeWriteSetPeek(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_union" :
				callEval = executeMemUnion(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_widening" :
				callEval = executeMemWidening(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_havoc" :
				callEval = executeHavocMem(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_new" :
				callEval = executeNewMem(state, pid, arguments, argumentValues,
						source);
				break;
			case "$mem_equals" :
				callEval = executeMemEquals(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_num_groups" :
				callEval = executeMemNumGroups(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_groups" :
				callEval = executeMemGroups(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_get_group" :
				callEval = executeMemGetGroup(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_to_pointers" :
				callEval = executeMemToPointers(state, pid, arguments,
						argumentValues, source);
				break;
			case "$mem_to_pointers_size" :
				callEval = executeMemToPointersSize(state, pid, arguments,
						argumentValues, source);
				break;
			default :
				throw new CIVLInternalException(
						"Unknown mem function: " + functionName, source);
		}
		return callEval;
	}

	/**
	 * <p>
	 * Executing the system function:<code>$write_set_push()</code>. <br>
	 * <br>
	 * 
	 * Push an empty write set onto write set stack associated with the calling
	 * process.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeWriteSetPush(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) {
		// SymbolicExpression writeSet = argumentValues[0];

		state = stateFactory.pushEmptyWrite(state, pid);
		// if (writeSet.operator() == SymbolicOperator.TUPLE) {
		// SymbolicExpression pointerArray = universe.tupleRead(writeSet,
		// oneObject);
		// NumericExpression arrayLength = universe.length(pointerArray);
		// int arrayLengthInt = ((IntegerNumber) universe
		// .extractNumber(arrayLength)).intValue();
		//
		// for (int i = 0; i < arrayLengthInt; i++)
		// state = stateFactory.addWriteRecords(state, pid,
		// universe.arrayRead(pointerArray, universe.integer(i)));
		// }
		return new Evaluation(state, null);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$write_set_pop($mem * m)</code>. <br>
	 * <br>
	 * 
	 * Pop a write set w out of the write set stack associated with the calling
	 * process. Assign write set w' to the object refered by the given reference
	 * m, where w' is a subset of w. <code>w - w'</code> is a set of unreachable
	 * memory locaiton references.
	 * 
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeWriteSetPop(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		// SymbolicExpression memPointer = argumentValues[0];
		CIVLType memType = typeFactory.systemType(ModelConfiguration.MEM_TYPE);
		// Evaluation eval = evaluator.dereference(source, state, process,
		// memPointer, false, true);

		// state = eval.state;

		SymbolicExpression memValue;
		SymbolicExpression pointerArray;
		SymbolicTupleType memValueType;
		LinkedList<SymbolicExpression> memValueComponents = new LinkedList<>();
		DynamicWriteSet writeSet = stateFactory.peekWriteSet(state, pid);
		int size = 0;

		state = stateFactory.popWriteSet(state, pid);
		memValueType = (SymbolicTupleType) memType.getDynamicType(universe);
		for (SymbolicExpression pointer : writeSet) {
			int referredDyscope = stateFactory
					.getDyscopeId(symbolicUtil.getScopeValue(pointer));

			if (referredDyscope < 0)
				continue;
			memValueComponents.add(pointer);
			size++;
		}
		pointerArray = universe.array(typeFactory.pointerSymbolicType(),
				memValueComponents);
		memValueComponents.clear();
		memValueComponents.add(universe.integer(size));
		memValueComponents.add(pointerArray);
		memValue = universe.tuple(memValueType, memValueComponents);
		// state = primaryExecutor.assign(source, state, pid, memPointer,
		// memValue);
		// eval.state = state;
		// eval.value = memValue;
		return new Evaluation(state, memValue);
	}

	private Evaluation executeWriteSetPeek(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		CIVLType memType = typeFactory.systemType(ModelConfiguration.MEM_TYPE);
		// Evaluation eval = evaluator.dereference(source, state, process,
		// memPointer, false, true);

		// state = eval.state;

		SymbolicExpression memValue;
		SymbolicExpression pointerArray;
		SymbolicTupleType memValueType;
		LinkedList<SymbolicExpression> memValueComponents = new LinkedList<>();
		DynamicWriteSet writeSet = stateFactory.peekWriteSet(state, pid);
		int size = 0;

		memValueType = (SymbolicTupleType) memType.getDynamicType(universe);
		for (SymbolicExpression pointer : writeSet) {
			int referredDyscope = stateFactory
					.getDyscopeId(symbolicUtil.getScopeValue(pointer));

			if (referredDyscope < 0)
				continue;
			memValueComponents.add(pointer);
			size++;
		}
		pointerArray = universe.array(typeFactory.pointerSymbolicType(),
				memValueComponents);
		memValueComponents.clear();
		memValueComponents.add(universe.integer(size));
		memValueComponents.add(pointerArray);
		memValue = universe.tuple(memValueType, memValueComponents);
		return new Evaluation(state, memValue);
	}

	private Evaluation executeMemUnion(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mem0 = argumentValues[0];
		SymbolicExpression mem1 = argumentValues[1];
		SymbolicExpression mem0ptrs[] = memObject2PointerArray(mem0);
		SymbolicExpression mem1ptrs[] = memObject2PointerArray(mem1);
		TreeSet<SymbolicExpression> set = new TreeSet<>(universe.comparator());

		for (TreeSet<SymbolicExpression> ret : wsUnionOperator.apply(mem0ptrs,
				mem1ptrs))
			set.addAll(ret);
		int newSize = set.size();
		SymbolicExpression newPointerArray = universe
				.array(typeFactory.pointerSymbolicType(), set);
		List<SymbolicExpression> tupleComponents = new LinkedList<>();

		tupleComponents.add(universe.integer(newSize));
		tupleComponents.add(newPointerArray);
		return new Evaluation(state,
				universe.tuple((SymbolicTupleType) typeFactory
						.systemType(ModelConfiguration.MEM_TYPE)
						.getDynamicType(universe), tupleComponents));

	}

	private Evaluation executeMemEquals(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression[] ptrs0 = memObject2PointerArray(argumentValues[0]);
		SymbolicExpression[] ptrs1 = memObject2PointerArray(argumentValues[1]);
		boolean result = true;

		if (ptrs0.length == ptrs1.length) {
			for (int i = 0; i < ptrs0.length; i++)
				if (!ptrs0[i].equals(ptrs1[i])) {
					result = false;
					break;
				}
			return new Evaluation(state, universe.bool(result));
		}
		return new Evaluation(state, universe.falseExpression());
	}

	private Evaluation executeMemGroups(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointers[] = this
				.memObject2PointerArray(argumentValues[0]);
		SymbolicExpression outputPointer = argumentValues[1];
		Iterable<TreeSet<SymbolicExpression>> groups = wsGroupOperator
				.apply(pointers);
		List<SymbolicExpression> memValueComponents = new LinkedList<>();
		SymbolicTupleType memValueType = (SymbolicTupleType) typeFactory
				.systemType(ModelConfiguration.MEM_TYPE)
				.getDynamicType(universe);
		List<SymbolicExpression> groupsArray = new LinkedList<>();

		for (TreeSet<SymbolicExpression> group : groups) {
			SymbolicExpression pointerArray = universe
					.array(typeFactory.pointerSymbolicType(), group);

			memValueComponents.clear();
			memValueComponents.add(universe.integer(group.size()));
			memValueComponents.add(pointerArray);
			groupsArray.add(universe.tuple(memValueType, memValueComponents));
		}
		state = primaryExecutor.assign(source, state, pid,
				symbolicUtil.parentPointer(outputPointer),
				universe.array(memValueType, groupsArray));
		return new Evaluation(state, universe.nullExpression());
	}

	private Evaluation executeMemGetGroup(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointerSet[] = memObject2PointerArray(
				argumentValues[0]);
		SymbolicExpression keySet[] = memObject2PointerArray(argumentValues[1]);

		if (keySet.length <= 0)
			throw new CIVLInternalException(
					"$mem_get_group($mem m, $mem key) function was used incorrectly, "
							+ "the 'key' argument must be a non-empty $mem type object",
					source);

		SymbolicExpression keyRoot = symbolicUtil.isPointerToHeap(keySet[0])
				? symbolicUtil.getPointer2MemoryBlock(keySet[0])
				: symbolicUtil.makePointer(keySet[0],
						universe.identityReference());

		pointerSet = wsGroupOperator.getGroup(pointerSet, keyRoot);
		return new Evaluation(state, pointerArray2MemObj(pointerSet));
	}

	private Evaluation executeMemNumGroups(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression pointers[] = this
				.memObject2PointerArray(argumentValues[0]);

		return new Evaluation(state,
				universe.integer(wsGroupOperator.numGroups(pointers)));
	}

	private Evaluation executeMemWidening(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mem = argumentValues[0];
		SymbolicExpression pointers[] = memObject2PointerArray(mem);
		TreeSet<SymbolicExpression> widenedPointers = new TreeSet<>(
				universe.comparator());

		for (TreeSet<SymbolicExpression> ret : wsWideningOperator
				.apply(pointers))
			widenedPointers.addAll(ret);
		SymbolicExpression pointerArray = universe
				.array(typeFactory.pointerSymbolicType(), widenedPointers);
		SymbolicExpression newSize = universe.length(pointerArray);

		mem = universe.tuple(
				(SymbolicTupleType) typeFactory
						.systemType(ModelConfiguration.MEM_TYPE)
						.getDynamicType(universe),
				Arrays.asList(newSize, pointerArray));
		return new Evaluation(state, mem);
	}

	private Evaluation executeMemToPointers(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mem = argumentValues[0];
		SymbolicExpression pointer2array = argumentValues[1];
		SymbolicExpression pointers[] = memObject2PointerArray(mem);
		SymbolicExpression pointerArray = universe.array(typeFactory
				.pointerType(typeFactory.voidType()).getDynamicType(universe),
				pointers);

		state = primaryExecutor.assign(source, state, pid, pointer2array,
				pointerArray);
		return new Evaluation(state, universe.nullExpression());
	}

	private Evaluation executeMemToPointersSize(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mem = argumentValues[0];
		NumericExpression memSize = (NumericExpression) universe.tupleRead(mem,
				zeroObject);

		return new Evaluation(state, memSize);
	}

	/**
	 * <p>
	 * Executing the system function:<code>$havoc_mem($mem m)</code>. <br>
	 * <br>
	 * Semantics: The function assigns a fresh new symbolic constant to every
	 * memory location in the memory location set represented by m. <br>
	 * 
	 * Notice that currently we do an <strong>compromise</strong> for refreshing
	 * array elements in m: For an array element e in array a in m, we do NOT
	 * assign e a fresh new constant but instead assign the array a a fresh new
	 * constant. The reason is: A non-concrete array write will prevent states
	 * from being canonicalized into a seen state. For example:
	 * 
	 * <code>
	 * $input int N, X;
	 * $assume(N > 0 && X > 0 && N > X);
	 * int a[N];
	 * 
	 * LOOP_0: while (true) {
	 *   a[X] = 0;
	 *   $havoc(&a[X]);
	 * }
	 * 
	 * LOOP_1: while (true) {
	 *   a[X] = 0;
	 *   $havoc(&a);
	 * }
	 * </code> Loop 1 will never converge but the value of a keeps growing. Loop
	 * 2 will converge.
	 * </p>
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
	 *            The {@link CIVLSource} associates to the function call.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeHavocMem(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression memObj = argumentValues[0];
		SymbolicExpression stateValue = argumentValues[1];
		State originalState = modelFactory
				.statenullConstantValue() == stateValue
						? state
						: stateFactory.getStateByReference(
								modelFactory.getStateRef(stateValue));
		SymbolicExpression pointers[] = memObject2PointerArray(memObj);
		BooleanExpression returnedValue = universe.trueExpression();

		Pair<State, List<AssignableRefreshment>> refreshes = wsRefresher
				.refresh(errSideEffectFreeEvaluator, originalState, state, pid,
						Arrays.asList(pointers), source);

		state = refreshes.left;
		for (AssignableRefreshment refresh : refreshes.right) {
			state = primaryExecutor.assign(source, state, pid, refresh.pointer,
					refresh.refreshedObject);
			if (!refresh.assumption.isTrue())
				returnedValue = universe.and(returnedValue, refresh.assumption);
		}
		return new Evaluation(state, returnedValue);
	}

	private Evaluation executeNewMem(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		CIVLType memType = typeFactory.systemType(ModelConfiguration.MEM_TYPE);
		SymbolicTupleType symbolicMemType = (SymbolicTupleType) memType
				.getDynamicType(universe);
		List<SymbolicExpression> memObjectComponents = new LinkedList<>();

		memObjectComponents.add(universe.zeroInt());
		memObjectComponents.add(universe
				.array(typeFactory.pointerSymbolicType(), Arrays.asList()));
		return new Evaluation(state,
				universe.tuple(symbolicMemType, memObjectComponents));
	}

	private SymbolicExpression[] memObject2PointerArray(
			SymbolicExpression memObj) {
		NumericExpression memSize = (NumericExpression) universe
				.tupleRead(memObj, zeroObject);
		SymbolicExpression pointerArray = universe.tupleRead(memObj, oneObject);
		Number memSizeConcrete = universe.extractNumber(memSize);
		assert memSizeConcrete != null : "The size of $mem obj shall never be non-concrete";

		int memSizeInt = ((IntegerNumber) memSizeConcrete).intValue();
		SymbolicExpression pointers[] = new SymbolicExpression[memSizeInt];

		for (int i = 0; i < memSizeInt; i++)
			pointers[i] = universe.arrayRead(pointerArray, universe.integer(i));
		return pointers;
	}

	private SymbolicExpression pointerArray2MemObj(
			SymbolicExpression[] pointers) {
		SymbolicExpression pointerArray = universe
				.array(typeFactory.pointerSymbolicType(), pointers);
		List<SymbolicExpression> memValueComponents = new LinkedList<>();
		SymbolicTupleType memValueType = (SymbolicTupleType) typeFactory
				.systemType(ModelConfiguration.MEM_TYPE)
				.getDynamicType(universe);

		memValueComponents.add(universe.integer(pointers.length));
		memValueComponents.add(pointerArray);
		return universe.tuple(memValueType, memValueComponents);
	}
}
