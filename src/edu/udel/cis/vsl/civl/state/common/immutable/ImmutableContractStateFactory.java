package edu.udel.cis.vsl.civl.state.common.immutable;

import java.util.BitSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.ContractConditionGenerator;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.contract.ContractEvaluator;
import edu.udel.cis.vsl.civl.semantics.contract.ContractExecutor;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.transform.IF.ContractTransformer;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class represents a {@link StateFactory} for CIVL contracts-system mode. <br>
 * CIVL contract-system mode lets CIVL works in a significantly different
 * mechanism with regular CIVL verifier: CIVL verifies functions separately with
 * its contracts. Calls on contracted functions will be replaced by applying
 * such a relation {requirements hold ==>(implies) ensures hold}.
 * 
 * @author ziqing
 *
 */
public class ImmutableContractStateFactory extends ImmutableStateFactory
		implements StateFactory {
	/**
	 * A reference to an evaluator which is used to evaluator requirements when
	 * building an initial state.
	 */
	private ContractEvaluator evaluator;

	private ContractExecutor executor;

	private ContractConditionGenerator conditionGenerator;

	/**
	 * Create a {@link StateFactory} for CIVL contracts-system mode.
	 * 
	 */
	public ImmutableContractStateFactory(ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, MemoryUnitFactory memFactory,
			GMCConfiguration gmcConfig, CIVLConfiguration config,
			ContractEvaluator evaluator, ContractExecutor executor) {
		super(modelFactory, symbolicUtil, memFactory, gmcConfig, config);
		this.evaluator = evaluator;
		this.conditionGenerator = evaluator.contractConditionGenerator();
		this.executor = executor;
	}

	/**
	 * Creates a initial state which starts from a specific function. The state
	 * will be initialized with the contracts of the function.
	 * 
	 * @param functionModel
	 * @return
	 * @throws CIVLHeapException
	 * @throws UnsatisfiablePathConditionException
	 */
	public ImmutableState initialState(CIVLFunction functionModel,
			int numProcesses) throws CIVLHeapException,
			UnsatisfiablePathConditionException {
		// The whole CIVL models:
		Model model = functionModel.model();
		// Root scope is the scope outside of the function:
		Scope rootScope;
		// An ImmutableContractState:
		ImmutableState initialState;
		SymbolicExpression args[] = new SymbolicExpression[functionModel
				.parameters().size()];
		Variable atomicVar = modelFactory.atomicLockVariableExpression()
				.variable();
		Variable timeCountVar = modelFactory.timeCountVariable();
		Variable genRoot, symbolicConstantCounter;
		FunctionContract contracts = functionModel.functionContract();
		List<Pair<PointerSetExpression, Integer>> validConsequences = new LinkedList<>();
		BooleanExpression context;
		Evaluation eval;
		List<AssignStatement> globalAssignments;
		String[] processes = new String[numProcesses];

		// TODO: this is not correct:
		globalAssignments = ContractTransformer.getGlobalStatements(model);
		rootScope = model.system().outerScope();
		genRoot = rootScope.variable(ModelConfiguration.GENERAL_ROOT);
		initialState = new ImmutableState(new ImmutableProcessState[0],
				new ImmutableDynamicScope[0], universe.trueExpression());
		if (functionModel.isRootFunction())
			functionModel.setOuterScope(rootScope);
		// Push root scope and function scope:
		initialState = pushRootScope(initialState, numProcesses, rootScope);
		for (int pid = 0; pid < numProcesses; pid++)
			initialState = pushCallStack2(initialState, pid, functionModel, 0,
					args, -1);
		for (int pid = 0; pid < processes.length; pid++) {
			int processIdentifier = initialState.getProcessState(pid)
					.identifier();

			processes[pid] = "p" + processIdentifier + " (id = " + pid + ")";
		}
		// Initializing global arguments:
		initialState = this.setVariable(initialState, atomicVar.vid(), 0,
				undefinedProcessValue);
		if (timeCountVar != null)
			initialState = setVariable(initialState, timeCountVar.vid(), 0,
					universe.zeroInt());
		symbolicConstantCounter = rootScope
				.variable(ModelConfiguration.SYMBOLIC_CONSTANT_COUNTER);
		if (symbolicConstantCounter != null)
			initialState = setVariable(initialState, symbolicConstantCounter,
					0, universe.zeroInt());
		// Initializing arguments and memory spaces:
		for (int pid = 0; pid < numProcesses; pid++) {
			int rootDyscopeId = initialState.getDyscope(pid, rootScope);

			if (genRoot != null)
				initialState = this.setVariable(initialState, genRoot, pid,
						modelFactory.scopeValue(rootDyscopeId));
			for (Variable var : functionModel.parameters()) {
				Expression varVal;

				// Temporarily set "var" as an input variable, so that its
				// value can be initialized as a symbolic constant:
				// if (!var.type().isPointerType()) {
				var.setIsInput(true);
				varVal = modelFactory.initialValueExpression(var.getSource(),
						var);
				eval = evaluator.evaluate(initialState, pid, varVal);
				var.setIsInput(false);
				initialState = (ImmutableState) eval.state;
				initialState = this.setVariable(initialState, var, pid,
						eval.value);
			}
		}
		for (int pid = 0; pid < numProcesses; pid++) {
			for (AssignStatement assign : globalAssignments) {
				eval = evaluator.evaluate(initialState, pid, assign.rhs());
				initialState = (ImmutableState) executor.assign(eval.state,
						pid, processes[pid], assign.getLhs(), eval.value);
			}
		}
		/******* Necessary derivation on contracts *******/
		// PHASE 1: Derives contracts to reasonable boolean expressions:
		Iterator<Expression> requiresIter = contracts.defaultBehavior()
				.preconditions().iterator();
		context = universe.trueExpression();
		for (int pid = 0; pid < numProcesses; pid++) {
			while (requiresIter.hasNext()) {
				eval = conditionGenerator.deriveExpression(initialState, pid,
						requiresIter.next());
				initialState = (ImmutableState) eval.state;
				context = universe.and(context, (BooleanExpression) eval.value);
			}
		}

		// PHASE 2: Reasoning some clauses that need special handling:
		for (int pid = 0; pid < numProcesses; pid++) {
			for (Pair<Expression, Integer> guess : functionModel
					.getPossibleValidConsequences()) {
				PointerSetExpression mem;

				eval = conditionGenerator.deriveExpression(initialState, pid,
						guess.left);
				initialState = (ImmutableState) eval.state;
				if (isRequirementConsequence(context,
						(BooleanExpression) eval.value)) {
					mem = (PointerSetExpression) ((UnaryExpression) guess.left)
							.operand();
					validConsequences.add(new Pair<>(mem, guess.right));
				}
			}
		}

		// PHASE 2.1 Special handling on some clauses:
		conditionGenerator.setValidConsequences(validConsequences);
		for (int pid = 0; pid < numProcesses; pid++)
			initialState = concretizeAllPointers(initialState, pid);

		// PHASE 3: Evaluating contracts phase:
		Reasoner reasoner;

		requiresIter = contracts.defaultBehavior().preconditions().iterator();
		context = initialState.getPathCondition();
		for (int pid = 0; pid < numProcesses; pid++)
			while (requiresIter.hasNext()) {
				BooleanExpression pred;
				Expression require = requiresIter.next();

				eval = evaluator.evaluate(initialState, pid, require);
				initialState = (ImmutableState) eval.state;
				reasoner = universe.reasoner(context);
				pred = (BooleanExpression) eval.value;
				context = universe.and(context, pred);
				if (reasoner.getReducedContext().isFalse()) {
					SymbolicAnalyzer symbolicAnalyzer = evaluator
							.symbolicAnalyzer();

					evaluator.errorLogger().logSimpleError(require.getSource(),
							initialState, processes[pid],
							symbolicAnalyzer.stateInformation(initialState),
							ErrorKind.CONTRACT,
							"Unsatisfiable requirements: " + require);
				}
			}
		initialState = initialState.setPathCondition(context);
		return super.canonic(initialState, false, false, false,
				emptyHeapErrorSet);
	}

	/************************* Helper functions ************************/
	/**
	 * Currently, it deduces \valid axioms. TODO: support more
	 * 
	 * @param state
	 *            The current state;
	 * @param consequence
	 *            The axiom that will be deduced.
	 * @param pid
	 *            The PID of current process
	 * @param mem
	 *            The {@link MemExpression} related to the axiom
	 * @return
	 */
	private boolean isRequirementConsequence(BooleanExpression context,
			BooleanExpression consequence) {
		Reasoner reasoner;
		// Inference on consequences of requirements doesn't need path
		// conditions:
		reasoner = universe.reasoner(context);
		return reasoner.isValid(consequence);
	}

	/**
	 * Pushes the root scope into a process state as the very first scope when
	 * creating an initial state based on a single function. The root scope
	 * contains several variables created and will be used by the system. In
	 * contract system mode, each process has an unique dynamic scope instance
	 * of the root scope.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param rootScope
	 *            The lexical scope of the root scope
	 * @return
	 */
	private ImmutableState pushRootScope(ImmutableState state,
			int numProcesses, Scope rootScope) {
		ImmutableProcessState[] newProcesses = new ImmutableProcessState[numProcesses];
		SymbolicExpression[] values;
		ImmutableDynamicScope[] newScopes;
		int rootDyScopeId = dyscopeCount;
		BitSet bitSet = new BitSet(numProcesses);
		Location location = modelFactory.location(rootScope.getSource(),
				rootScope);

		values = initialValues(rootScope);
		bitSet.set(0, numProcesses - 1);
		newScopes = state.copyAndExpandScopes();
		newScopes[rootDyScopeId] = new ImmutableDynamicScope(rootScope, -1, -1,
				values, bitSet, dyscopeCount++);

		for (int pid = 0; pid < numProcesses; pid++) {
			state = createNewProcess(state);
			newProcesses[pid] = state.getProcessState(pid).push(
					stackEntry(location, rootDyScopeId,
							newScopes[rootDyScopeId].identifier()));
		}
		state = ImmutableState.newState(state, newProcesses, newScopes, null);
		return state;
	}

	/**
	 * TODO:limitation: range can only go from 0 .. N with step 1
	 * 
	 * 
	 * Concretize all pointers that are proved as valid pointers.
	 * 
	 * @param state
	 * @param pid
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private ImmutableState concretizeAllPointers(State state, int pid)
			throws UnsatisfiablePathConditionException {
		Iterator<List<Integer>> mallocsIter = conditionGenerator
				.validPointersIterator();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";
		Evaluation eval;

		while (mallocsIter.hasNext()) {
			List<Integer> mallocIDs = mallocsIter.next();
			Scope scope = evaluator.getVerifyingFunction().outerScope();
			int dyscopeId = state.getDyscope(pid, scope);

			for (Integer i : mallocIDs) {
				MallocStatement mallocStmt = modelFactory.model().getMalloc(i);
				SymbolicExpression range;
				NumericExpression size;
				Pair<State, SymbolicExpression> ret;

				if (mallocStmt.getSizeExpression() != null) {
					eval = evaluator.evaluate(state, pid,
							mallocStmt.getSizeExpression());
					state = eval.state;
					range = eval.value;
					size = symbolicUtil.getHighOfRegularRange(range);
					// \valid(ptr + (0..n)) ==> there are (n + 1) objects in
					// heap:
					size = universe.add(size, universe.oneInt());
				} else
					size = universe.oneInt();
				ret = malloc(state, pid, dyscopeId, i,
						mallocStmt.getDynamicElementType(), size);
				state = ret.left;
				state = executor.assign(state, pid, process,
						mallocStmt.getLHS(), ret.right);
			}
		}
		return (ImmutableState) state;
	}
}
