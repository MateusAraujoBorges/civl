package edu.udel.cis.vsl.civl.library.collate;

import java.util.BitSet;

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
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

public class LibcollateExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {
	/**
	 * Field index for $collate_state.gstate:
	 */
	private final IntObject collate_state_gstate;

	/**
	 * Field index for $gcollate_state->$state:
	 */
	private final IntObject gcollate_state_state;

	/**
	 * Field index for $gcollate_state->status
	 */
	private final IntObject gcollate_state_status;

	public LibcollateExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		collate_state_gstate = universe
				.intObject(LibcollateConstants.COLLATE_STATE_GSTATE);
		gcollate_state_state = universe
				.intObject(LibcollateConstants.GCOLLATE_STATE_STATE);
		gcollate_state_status = universe
				.intObject(LibcollateConstants.GCOLLATE_STATE_STATUS);
	}

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$collate_complete" :
				callEval = executeCollateComplete(state, pid, process,
						arguments, argumentValues, source);
				break;
			case "$collate_arrived" :
				callEval = executeCollateArrived(state, pid, process, arguments,
						argumentValues, source);
				break;
			// case "$enter_collate_state":
			// callEval = executeEnterCollateState(state, pid, process,
			// arguments,
			// argumentValues, source);
			// break;
			// case "$exit_collate_state":
			// callEval = executeExitCollateState(state, pid, process,
			// arguments,
			// argumentValues, source);
			// break;
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

	// /**
	// * $system void $exit_collate_state($collate_state cs, $state rs);
	// *
	// * @param state
	// * @param pid
	// * @param process
	// * @param arguments
	// * @param argumentValues
	// * @param source
	// * @return
	// * @throws UnsatisfiablePathConditionException
	// */
	// private Evaluation executeExitCollateState(State state, int pid,
	// String process, Expression[] arguments,
	// SymbolicExpression[] argumentValues, CIVLSource source)
	// throws UnsatisfiablePathConditionException {
	// SymbolicExpression colStatePointer = argumentValues[0], colStateComp;
	// Evaluation eval;
	// SymbolicExpression rsVal, newColStateRef;
	// int rsID, newColStateID;
	// State realState = null;
	// SymbolicExpression ghandle, ghandleStatePointer;
	//
	// eval = this.evaluator.dereference(source, state, process, arguments[0],
	// colStatePointer, false);
	// state = eval.state;
	// colStateComp = eval.value;
	// ghandle = universe.tupleRead(colStateComp, oneObject);
	// rsVal = universe.tupleRead(colStateComp, twoObject);
	// rsID = this.modelFactory.getStateRef(source, rsVal);
	// realState = stateFactory.getStateByReference(rsID);
	// newColStateID = stateFactory.saveState(state, pid);
	// if (this.civlConfig.debugOrVerbose() || this.civlConfig.showStates()
	// || civlConfig.showSavedStates()) {
	// civlConfig.out().println(this.symbolicAnalyzer.stateToString(
	// stateFactory.getStateByReference(newColStateID)));
	// }
	// newColStateRef = this.modelFactory.stateValue(newColStateID);
	// ghandleStatePointer = symbolicUtil.extendPointer(ghandle,
	// universe.tupleComponentReference(universe.identityReference(),
	// gcollate_state_state));
	// realState = this.primaryExecutor.assign(source, realState, process,
	// ghandleStatePointer, newColStateRef);
	// realState = realState.setPathCondition(universe
	// .and(realState.getPathCondition(), state.getPathCondition()));
	// return new Evaluation(realState, null);
	// }

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
	// private Evaluation executeEnterCollateState(State state, int pid,
	// String process, Expression[] arguments,
	// SymbolicExpression[] argumentValues, CIVLSource source)
	// throws UnsatisfiablePathConditionException {
	// Evaluation eval;
	// SymbolicExpression colStatePointer = argumentValues[0], colStateComp,
	// gstateHandle, gstate, colStateVal;
	// int colStateID, realStateID;
	// State colState = null;
	// SymbolicExpression realStateRef;
	//
	// realStateID = stateFactory.saveState(state, pid);
	// eval = this.evaluator.dereference(source, state, process, arguments[0],
	// colStatePointer, false);
	// state = eval.state;
	// colStateComp = eval.value;
	// gstateHandle = universe.tupleRead(colStateComp, oneObject);
	// eval = this.evaluator.dereference(source, state, process, arguments[0],
	// gstateHandle, false);
	// state = eval.state;
	// gstate = eval.value;
	// colStateVal = universe.tupleRead(gstate, gcollate_state_state);
	// colStateID = this.modelFactory.getStateRef(source, colStateVal);
	// colState = stateFactory.getStateByReference(colStateID);
	// realStateRef = modelFactory.stateValue(realStateID);
	// if (this.civlConfig.debugOrVerbose() || this.civlConfig.showStates()
	// || civlConfig.showSavedStates()) {
	// civlConfig.out().println(this.symbolicAnalyzer.stateToString(
	// stateFactory.getStateByReference(realStateID)));
	// }
	// colStateComp = universe.tupleWrite(colStateComp, twoObject,
	// realStateRef);
	// colState = primaryExecutor.assign(source, colState, process,
	// colStatePointer, colStateComp);
	// return new Evaluation(colState, null);
	// }

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
		SymbolicExpression gcollateStateHandle, gcollateState, symStateRef;
		int scopeId = modelFactory.getScopeId(source, scopeValue);
		int stateRef, nprocs, place, resultRef;
		Evaluation eval;
		State mono, resultState, coState;

		// Take a snapshot on the given state for the calling process:
		mono = stateFactory.getStateSnapshot(state, pid, scopeId);
		symPlace = (NumericExpression) universe.tupleRead(collateState,
				zeroObject);
		gcollateStateHandle = universe.tupleRead(collateState,
				collate_state_gstate);
		eval = evaluator.dereference(source, state, process, arguments[0],
				gcollateStateHandle, false, true);
		state = eval.state;
		gcollateState = eval.value;
		place = ((IntegerNumber) universe.extractNumber(symPlace)).intValue();
		nprocs = ((IntegerNumber) universe.extractNumber(symNprocs)).intValue();
		symStateRef = universe.tupleRead(gcollateState, gcollate_state_state);
		// If gcollate->$state == $state_null, then create a empty state first:
		if (modelFactory.statenullConstantValue().equals(symStateRef))
			coState = stateFactory.emptyState(nprocs);
		else {
			stateRef = modelFactory.getStateRef(source, symStateRef);
			coState = stateFactory.getStateByReference(stateRef);
			assert coState != null;
		}
		resultState = stateFactory.addInternalProcess(coState, mono, place);
		resultRef = stateFactory.saveState(resultState, pid).left;
		if (this.civlConfig.debugOrVerbose() || this.civlConfig.showStates()
				|| civlConfig.showSavedStates()) {
			civlConfig.out().println(this.symbolicAnalyzer.stateToString(
					stateFactory.getStateByReference(resultRef)));
		}
		symStateRef = modelFactory.stateValue(resultRef);
		gcollateState = universe.tupleWrite(gcollateState, gcollate_state_state,
				symStateRef);
		state = this.primaryExecutor.assign(source, state, pid,
				gcollateStateHandle, gcollateState);
		return new Evaluation(state, null);
	}

	/**
	 * A system implementation of the <code>$collate_complete</code>. Make it a
	 * system function so that it can be used as a guard expression.
	 * 
	 * @param state
	 *            The program state when this function is called.
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the calling process
	 * @param arguments
	 *            An array of {@link Expression}s for actual parameters
	 * @param values
	 *            An array of {@link SymbolicExpression}s for values of actual
	 *            parameters.
	 * @param source
	 *            The CIVLSource associates to the function call.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeCollateComplete(State state, int pid,
			String process, Expression[] arguments, SymbolicExpression[] values,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression colState = values[0];
		NumericExpression nprocs;
		SymbolicExpression gstateHanlde = universe.tupleRead(colState,
				collate_state_gstate);
		SymbolicExpression gstate, statusArray;
		Evaluation eval;

		eval = evaluator.dereference(source, state, process, arguments[0],
				gstateHanlde, false, true);
		gstate = eval.value;
		statusArray = universe.tupleRead(gstate, gcollate_state_status);
		nprocs = universe.length(statusArray);

		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		BooleanExpression pred;
		SymbolicExpression status = universe.arrayRead(statusArray, i);

		// forall i : [0, nprocs) that status[i] == 1 (ARRIVED) || status[i] ==
		// 2 (DEPARTED):
		pred = universe.equals(status, one);
		pred = universe.or(universe.equals(status, two), pred);
		pred = universe.forallInt(i, zero, nprocs, pred);
		eval.value = pred;
		return eval;
	}

	/**
	 * * A system implementation of the <code>$collate_arrived</code>. Make it a
	 * system function so that it can be used as a guard expression.
	 * 
	 * @param state
	 *            The program state when this function is called.
	 * @param pid
	 *            The PID of the calling process
	 * @param process
	 *            The String identifier of the calling process
	 * @param arguments
	 *            An array of {@link Expression}s for actual parameters
	 * @param values
	 *            An array of {@link SymbolicExpression}s for values of actual
	 *            parameters.
	 * @param source
	 *            The CIVLSource associates to the function call.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeCollateArrived(State state, int pid,
			String process, Expression[] arguments, SymbolicExpression[] values,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression colState = values[0];
		SymbolicExpression range = values[1];

		SymbolicExpression gstateHanlde = universe.tupleRead(colState,
				collate_state_gstate);
		SymbolicExpression gstate, statusArray;
		Evaluation eval;

		eval = evaluator.dereference(source, state, process, arguments[0],
				gstateHanlde, false, true);
		gstate = eval.value;
		statusArray = universe.tupleRead(gstate, gcollate_state_status);

		BooleanExpression pred = universe.trueExpression();
		SymbolicExpression status;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		BitSet rangeVal = symbolicUtil.range2BitSet(range, reasoner);

		for (int i = rangeVal.nextSetBit(0); i >= 0; i = rangeVal
				.nextSetBit(i + 1)) {
			BooleanExpression claim;

			if (i < 0) {
				// Waiting for non-existed processes means waiting for nothing:
				claim = trueValue;
			} else {
				status = universe.arrayRead(statusArray, universe.integer(i));
				claim = universe.equals(status, one);
				claim = universe.or(universe.equals(status, two), claim);
			}
			pred = universe.and(pred, claim);
		}
		eval.value = pred;
		return eval;
	}
}
