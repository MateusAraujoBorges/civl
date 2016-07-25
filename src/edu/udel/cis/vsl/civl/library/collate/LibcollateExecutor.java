package edu.udel.cis.vsl.civl.library.collate;

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
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

public class LibcollateExecutor extends BaseLibraryExecutor
		implements LibraryExecutor {
	private final IntObject collate_state_gstate;

	private final IntObject gcollate_state_state;

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
	}

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
		case "$enter_collate_state":
			callEval = executeEnterCollateState(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$exit_collate_state":
			callEval = executeExitCollateState(state, pid, process, arguments,
					argumentValues, source);
			break;
		case "$collate_snapshot":
			callEval = executeCollateSnapshot(state, pid, process, arguments,
					argumentValues, source);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(
					"the function " + name + " of library pointer.cvh", source);
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
		SymbolicExpression colStatePointer = argumentValues[0], colStateComp;
		Evaluation eval;
		SymbolicExpression rsVal, newColStateRef;
		int rsID, newColStateID;
		State realState = null;
		SymbolicExpression ghandle, ghandleStatePointer;

		eval = this.evaluator.dereference(source, state, process, arguments[0],
				colStatePointer, false);
		state = eval.state;
		colStateComp = eval.value;
		ghandle = universe.tupleRead(colStateComp, oneObject);
		rsVal = universe.tupleRead(colStateComp, twoObject);
		rsID = this.modelFactory.getStateRef(source, rsVal);
		realState = stateFactory.getStateByReference(rsID);
		newColStateID = stateFactory.saveState(state, pid);
		if (this.civlConfig.debugOrVerbose() || this.civlConfig.showStates()
				|| civlConfig.showSavedStates()) {
			civlConfig.out().println(this.symbolicAnalyzer.stateToString(
					stateFactory.getStateByReference(newColStateID)));
		}
		newColStateRef = this.modelFactory.stateValue(newColStateID);
		ghandleStatePointer = symbolicUtil.extendPointer(ghandle,
				universe.tupleComponentReference(universe.identityReference(),
						gcollate_state_state));
		realState = this.primaryExecutor.assign(source, realState, process,
				ghandleStatePointer, newColStateRef);
		realState = realState.setPathCondition(universe
				.and(realState.getPathCondition(), state.getPathCondition()));
		return new Evaluation(realState, null);
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
		Evaluation eval;
		SymbolicExpression colStatePointer = argumentValues[0], colStateComp,
				gstateHandle, gstate, colStateVal;
		int colStateID, realStateID;
		State colState = null;
		SymbolicExpression realStateRef;

		realStateID = stateFactory.saveState(state, pid);
		eval = this.evaluator.dereference(source, state, process, arguments[0],
				colStatePointer, false);
		state = eval.state;
		colStateComp = eval.value;
		gstateHandle = universe.tupleRead(colStateComp, oneObject);
		eval = this.evaluator.dereference(source, state, process, arguments[0],
				gstateHandle, false);
		state = eval.state;
		gstate = eval.value;
		colStateVal = universe.tupleRead(gstate, gcollate_state_state);
		colStateID = this.modelFactory.getStateRef(source, colStateVal);
		colState = stateFactory.getStateByReference(colStateID);
		realStateRef = modelFactory.stateValue(realStateID);
		if (this.civlConfig.debugOrVerbose() || this.civlConfig.showStates()
				|| civlConfig.showSavedStates()) {
			civlConfig.out().println(this.symbolicAnalyzer.stateToString(
					stateFactory.getStateByReference(realStateID)));
		}
		colStateComp = universe.tupleWrite(colStateComp, twoObject,
				realStateRef);
		colState = primaryExecutor.assign(source, colState, process,
				colStatePointer, colStateComp);
		return new Evaluation(colState, null);
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
		int stateRef, nprocs, place, resultRef;
		Evaluation eval;
		State mono, resultState, coState;

		mono = stateFactory.getStateSnapshot(state, pid, scopeId);
		symPlace = (NumericExpression) universe.tupleRead(collateState,
				zeroObject);
		gcollateStateHandle = universe.tupleRead(collateState,
				collate_state_gstate);
		eval = evaluator.dereference(source, state, process, arguments[0],
				gcollateStateHandle, false);
		state = eval.state;
		gcollateState = eval.value;
		place = ((IntegerNumber) universe.extractNumber(symPlace)).intValue();
		nprocs = ((IntegerNumber) universe.extractNumber(symNprocs)).intValue();
		symStateId = universe.tupleRead(gcollateState, gcollate_state_state);
		stateRef = modelFactory.getStateRef(source, symStateId);
		if (stateRef == -1) // TODO: hide this information
			coState = stateFactory.emptyState(nprocs);
		else
			coState = stateFactory.getStateByReference(stateRef);
		resultState = stateFactory.combineStates(coState, mono, place);
		resultRef = stateFactory.saveState(resultState, pid);
		// System.out.println(this.symbolicAnalyzer
		// .stateToString(stateFactory.getStateByReference(resultRef)));
		symStateId = modelFactory.stateValue(resultRef);
		gcollateState = universe.tupleWrite(gcollateState, gcollate_state_state,
				symStateId);
		state = this.primaryExecutor.assign(source, state, process,
				gcollateStateHandle, gcollateState);
		return new Evaluation(state, null);
	}
}
