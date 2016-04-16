package edu.udel.cis.vsl.civl.kripke.common;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public class ContractEnabler extends PointeredEnabler implements Enabler {

	public ContractEnabler(StateFactory stateFactory, Evaluator evaluator,
			SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, LibraryEnablerLoader libLoader,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig,
			ContractConditionGenerator conditionGenerator) {
		super(stateFactory, evaluator, symbolicAnalyzer, memUnitFactory,
				libLoader, errorLogger, civlConfig, conditionGenerator);
	}

	@Override
	public List<Transition> enabledTransitionsOfProcess(State state, int pid) {
		ProcessState procState = state.getProcessState(pid);

		// If caller is a $contractVerify statement, block until all arrived:
		if (procState.stackSize() > 1) {
			StackEntry stackEntry = procState.peekSecondLastStack();

			if (stackEntry.location().getSoleOutgoing().statementKind() == StatementKind.CONTRACT_VERIFY) {
				// Read the _mpi_sync_guard variable to
			}
		}

		return this.enabledTransitionsOfProcess(state, pid,
				new HashMap<Integer, Map<Statement, BooleanExpression>>(0));
	}

}
