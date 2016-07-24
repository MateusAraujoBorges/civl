package edu.udel.cis.vsl.civl.library.collate;

import java.util.Arrays;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

public class LibcollateExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {

	public LibcollateExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
	}

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$enter_collate_state" :
				callEval = executeEnterCollateState(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$exit_collate_state" :
				callEval = executeExitCollateState(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$collate_snapshot" :
				callEval = executeCollateSnapshot(state, pid, process,
						arguments, argumentValues, source);
				break;
			default :
				throw new CIVLUnimplementedFeatureException(
						"the function " + name + " of library pointer.cvh",
						source);
		}
		return callEval;
	}

	/**
	 * $system void $exit_collate_state($collate_state cs, $state rs);
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
	private Evaluation executeExitCollateState(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression rsVal = argumentValues[1],
				colStateVal = argumentValues[0], newColStateRef;
		@SuppressWarnings("unused")
		int rsID = this.symbolicUtil.extractInt(source,
				(NumericExpression) rsVal);
		State realState = null;
		SymbolicExpression ghandle = universe.tupleRead(colStateVal, oneObject),
				ghandleStatePointer;

		// TODO realState=stateFactory.getState(rsID);
		// TODO realState=stateFactory.subsitute(realState);
		try {
			state = stateFactory.canonic(state, false, false, false, null);
		} catch (CIVLHeapException e) {
			throw new UnsatisfiablePathConditionException();
		}
		newColStateRef = this.universe.tuple(typeFactory.stateSymbolicType(),
				Arrays.asList(universe.integer(state.getCanonicId())));
		ghandleStatePointer = symbolicUtil.extendPointer(ghandle,
				universe.tupleComponentReference(universe.identityReference(),
						twoObject));
		realState = this.primaryExecutor.assign(source, realState, process,
				ghandleStatePointer, newColStateRef);
		return new Evaluation(realState, null);
	}

	@SuppressWarnings("unused")
	private Evaluation getState(State state, SymbolicExpression colstate,
			CIVLSource source, String process)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression gstateHandle = universe.tupleRead(colstate,
				oneObject);
		Evaluation eval = this.evaluator.dereference(source, state, process,
				null, gstateHandle, false);
		SymbolicExpression gstate = eval.value;

		return new Evaluation(eval.state,
				universe.tupleRead(gstate, twoObject));
	}

	/**
	 * $system $state $enter_collate_state($collate_state cs);
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
	private Evaluation executeEnterCollateState(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression colStateVal = universe.tupleRead(
				universe.tupleRead(argumentValues[0], oneObject),
				this.twoObject);
		NumericExpression stateIDExpr = (NumericExpression) universe
				.tupleRead(colStateVal, zeroObject);
		@SuppressWarnings("unused")
		int colStateID = this.symbolicUtil.extractInt(source, stateIDExpr);
		State colState = null; // TODO stateFactory.getState(colStateID);
		SymbolicExpression realStateRef;

		try {
			state = this.stateFactory.canonic(state, true, true, true, null);
		} catch (CIVLHeapException e) {
			throw new UnsatisfiablePathConditionException();
		}
		realStateRef = universe.tuple(this.typeFactory.stateSymbolicType(),
				new SymbolicExpression[]{
						universe.integer(state.getCanonicId())});
		return new Evaluation(colState, realStateRef);
	}

	/**
	 * Executes the <code>$collate_snapshot($collate_state, int , $scope)</code>
	 * call.
	 * <p>
	 * Give a $collate_state which refers to a collate state, the number of all
	 * participant processes and a scope, the function should take a snapshot
	 * for the calling process on the current state then combine the snapshot
	 * with the collate state. The process call stack will be modified according
	 * to the given scope, it should guarantee that the top frame of the stack
	 * can reach the given scope (as long as the scope is reachable from the
	 * original call stack).
	 * </p>
	 * 
	 * @param state
	 *            The current state when calling the function
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            The {@link Expression} array which represents expressions of
	 *            actual parameters.
	 * @param argumentValues
	 *            The {@link SymbolicExpression} array which represents values
	 *            of actual parameters
	 * @param source
	 *            The {@link CIVLSource} associates to the function call
	 * @return The {@link Evaluation} which contains the post-state after
	 *         execution and the returned value if it exists, otherwise it's
	 *         null.
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeCollateSnapshot(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		NumericExpression symNprocs = (NumericExpression) argumentValues[1];
		NumericExpression symPlace;
		SymbolicExpression collateState = argumentValues[0];
		SymbolicExpression scopeValue = argumentValues[2];
		SymbolicExpression gcollateStateHandle, gcollateState, symStateId;
		int scopeId = modelFactory.getScopeId(source, scopeValue);
		int stateRef, nprocs, place;
		int resultRef, monoRef;
		Evaluation eval;
		State mono;

		monoRef = stateFactory.getStateSnapshot(state, pid, scopeId);
		mono = stateFactory.getStateByReference(monoRef);
		symPlace = (NumericExpression) universe.tupleRead(collateState,
				zeroObject);
		gcollateStateHandle = universe.tupleRead(collateState, oneObject);
		eval = evaluator.dereference(source, state, process, arguments[0],
				gcollateStateHandle, false);
		state = eval.state;
		gcollateState = eval.value;
		symStateId = universe.tupleRead(gcollateState, twoObject);
		stateRef = modelFactory.getStateRef(source, symStateId);
		place = ((IntegerNumber) universe.extractNumber(symPlace)).intValue();
		nprocs = ((IntegerNumber) universe.extractNumber(symNprocs)).intValue();
		resultRef = stateFactory.combineStates(stateRef, mono, place, nprocs);
		// The mono state is uncessary to keep being saved any more:
		stateFactory.unsaveStateByReference(monoRef);
		symStateId = modelFactory.stateValue(resultRef);
		gcollateState = universe.tupleWrite(gcollateState, twoObject,
				symStateId);
		state = this.primaryExecutor.assign(source, state, process,
				gcollateStateHandle, gcollateState);
		return new Evaluation(state, null);
	}
}
