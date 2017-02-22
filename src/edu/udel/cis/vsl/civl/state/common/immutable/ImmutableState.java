/**
 * 
 */
package edu.udel.cis.vsl.civl.state.common.immutable;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * Implementation of State based on the Immutable Pattern. This class is not
 * entirely immutable; it has certain fields such as {@link #onStack} and
 * {@link #depth} used by the depth first search algorithm which can be
 * modified. But it has an "observationally immutable core" consisting of the
 * path condition, dynamic scopes, and process states. While these can also
 * change in certain restricted ways, these changes are not visible to a user
 * going through the State interface.
 * 
 * The path condition and equals methods are based solely on the observationally
 * immutable core.
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Timothy K. Zirkel (zirkel)
 * @author Tim McClory (tmcclory)
 * @author Ziqing Luo (ziqing)
 * @author Yihao Yan (yanyihao)
 * 
 */
public class ImmutableState implements State {

	/**
	 * A simple class implementing Iterable, backed by the array of process
	 * states. It is needed because this class must implement a method to return
	 * an Iterable over ProcessState. We have a field which is an array of
	 * ImmutableProcessState. This is the easiest way to get an Iterable of the
	 * right type. Only one needs to be created, so once it is created it is
	 * cached. (Due to Immutable Pattern.)
	 * 
	 * @author siegel
	 * 
	 */
	class ProcessStateIterable implements Iterable<ProcessState> {

		class ProcessStateIterator implements Iterator<ProcessState> {

			int pos = 0;

			@Override
			public boolean hasNext() {
				return pos < processStates.length;
			}

			@Override
			public ProcessState next() {
				ProcessState result = processStates[pos];

				pos++;
				return result;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		}

		@Override
		public Iterator<ProcessState> iterator() {
			return new ProcessStateIterator();
		}
	}

	/* *************************** Static Fields *************************** */

	/**
	 * The number of instances of this class that have been created since the
	 * class was loaded.
	 */
	static long instanceCount = 0;

	/* ************************** Instance Fields ************************** */

	/**
	 * The path condition, a non-null boolean-valued symbolic expression.
	 * 
	 */
	private BooleanExpression pathCondition;

	/**
	 * Snapshots queue array for MPI communicators, one MPI communicator has an
	 * corresponding snapshot queue.
	 */
	private ImmutableCollectiveSnapshotsEntry[][] snapshotsQueues;

	/**
	 * processes[i] contains the process of pid i. some entries may be null.
	 */
	private ImmutableProcessState[] processStates;

	/**
	 * The dynamic scopes. The scope at position i is the dynamic scope with
	 * dyscopeId i. The scope at index 0 is always the system scope.
	 */
	private ImmutableDynamicScope[] dyscopes;

	/**
	 * If this is a canonic state (unique representative of its equivalence
	 * class), this field is the unique state ID for that class. Otherwise, it
	 * is -1.
	 */
	private int canonicId = -1;

	/**
	 * Minimum depth at which this state has been encountered in DFS; used for
	 * finding minimal counterexample.
	 */
	private int depth = -1;

	/**
	 * If the hashcode has been computed, it is cached here.
	 */
	private int hashCode = -1;

	/**
	 * Has the hashcode on this state already been computed?
	 */
	private boolean hashed = false;

	/**
	 * The absolutely unique ID number of this state, among all states ever
	 * created in this run of the JVM.
	 */
	private final long instanceId = instanceCount++;

	/**
	 * Whether this state is on the DFS search stack.
	 */
	private boolean onStack = false;

	/**
	 * The iterable object over the process states, created once and cached here
	 * for future use.
	 */
	private Iterable<ProcessState> processStateIterable = null;

	/**
	 * The cached hash code of the array of process states.
	 */
	private int procHashCode = -1;

	/**
	 * Has the hash code of the process state array been computed and cached?
	 */
	private boolean procHashed = false;

	/**
	 * The cached hash code of the array of dynamic scopes.
	 */
	private int scopeHashCode = -1;

	/**
	 * Has the hash code of the dynamic scope array been computed and cached?
	 */
	private boolean scopeHashed = false;

	/**
	 * Has this state been seen in the DFS search?
	 */
	private boolean seen = false;

	/**
	 * Cached reference to the simplified version of this state.
	 */
	ImmutableState simplifiedState = null;

	/**
	 * True iff all successors during search are on the search stack.
	 */
	private boolean allSuccessorsOnStack = true;

	/**
	 * True iff all successors resulting from the enabled transitions have been
	 * visited during the search.
	 */
	private boolean allSuccessorsVisited = false;

	int[] collectibleCounts;

	/* *************************** Static Methods ************************** */

	/**
	 * This is a convenience method for constructing a new state from an old
	 * state where any number of the fields may have changed. Any or all of the
	 * three field arguments (processStates, dyscopes, pathCondition) may be
	 * null; a null entry indicates that the field has not changed, so the old
	 * value from the old state should be used in constructing the new state.
	 * 
	 * @param state
	 *            the old state
	 * @param processStates
	 *            new value for processStates field or null if the old value
	 *            should be re-used
	 * @param dyscopes
	 *            new value for the dyscopes field or null if the old value
	 *            should be re-used
	 * @param pathCondition
	 *            new value for the path condition or null if the old one should
	 *            be re-used
	 * @param collectibleCounts
	 *            the counts of collectible symbolic constants the name of which
	 *            have the prefix from
	 *            {@link ModelConfiguration#SYMBOL_PREFIXES}
	 * @return new ImmutableState with fields as specified
	 */
	static ImmutableState newState(ImmutableState state, ImmutableProcessState[] processStates,
			ImmutableDynamicScope[] dyscopes, BooleanExpression pathCondition) {
		ImmutableState result = new ImmutableState(processStates == null ? state.processStates : processStates,
				dyscopes == null ? state.dyscopes : dyscopes,
				pathCondition == null ? state.pathCondition : pathCondition);

		if (processStates == null && state.procHashed) {
			result.procHashed = true;
			result.procHashCode = state.procHashCode;
		}
		if (dyscopes == null && state.scopeHashed) {
			result.scopeHashed = true;
			result.scopeHashCode = state.scopeHashCode;
		}
		result.collectibleCounts = state.collectibleCounts;
		result.snapshotsQueues = state.snapshotsQueues;
		return result;
	}

	/* **************************** Constructors *************************** */

	/**
	 * Constructs new ImmutableState. The arrays are used as fields---the
	 * elements are not copied into a new array. All arguments must be non-null.
	 * Seen and onStack bits are set to false.
	 * 
	 * @param processStates
	 *            the array of process states, with the element in position i
	 *            being the state of process with PID i; entries may be null
	 * @param dyscopes
	 *            array of dynamic scopes, with element in position i being the
	 *            dynamic scope with dyscopeId i
	 * @param pathCondition
	 *            the path condition, a boolean-valued symbolic expression which
	 *            is assumed to hold in this state
	 */
	ImmutableState(ImmutableProcessState[] processStates, ImmutableDynamicScope[] dyscopes,
			BooleanExpression pathCondition) {
		assert processStates != null;
		assert dyscopes != null;
		assert pathCondition != null;
		this.processStates = processStates;
		this.dyscopes = dyscopes;
		this.pathCondition = pathCondition;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Implements the flyweight pattern for ImmutableDynamicScopes: if there
	 * already exists a dyscope which is equivalent to the given dyscope, return
	 * that one, otherwise, add the dyscope to the table and return it.
	 * 
	 * This method goes into the dyscope and replaces each individual symbolic
	 * expression with the canonic version of that symbolic expression.
	 * 
	 * @param dyscope
	 *            the dyscope to be flyweighted
	 * @param scopeMap
	 *            the map to use for flyweighting in which the key-value pairs
	 *            have the form (X,X) for all canonic objects X
	 * @return the unique representative of the dyscope's equivalence class
	 */
	private ImmutableDynamicScope canonic(ImmutableDynamicScope dyscope,
			Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap, SymbolicUniverse universe) {
		ImmutableDynamicScope canonicScope = scopeMap.get(dyscope);

		if (canonicScope == null) {
			dyscope.makeCanonic(universe);
			scopeMap.put(dyscope, dyscope);
			return dyscope;
		}
		return canonicScope;
	}

	/**
	 * Implements the flyweight pattern for ImmutableProcessState: if there
	 * already exists a process state which is equivalent to the given one,
	 * return that one, otherwise, add the process state to the table and return
	 * it.
	 * 
	 * @param processState
	 *            the process state to be flyweighted
	 * @param scopeMap
	 *            the map to use for flyweighting in which the key-value pairs
	 *            have the form (X,X) for all canonic objects X
	 * @return the unique representative of the process state's equivalence
	 *         class
	 */
	private ImmutableProcessState canonic(ImmutableProcessState processState,
			Map<ImmutableProcessState, ImmutableProcessState> processMap) {
		ImmutableProcessState canonicProcessState = processMap.get(processState);

		if (canonicProcessState == null) {
			processState.makeCanonic();
			processMap.put(processState, processState);
			return processState;
		}
		return canonicProcessState;
	}

	/**
	 * Prints a dyscope of a given id of this state to the given print stream.
	 * 
	 * @param out
	 *            The print stream to be used.
	 * @param dyscope
	 *            The dyscope to be printed.
	 * @param id
	 *            The id of the dyscope to be printed.
	 * @param prefix
	 *            The line prefix of the printing result.
	 */
	private void printImmutableDynamicScope(PrintStream out, ImmutableDynamicScope dyscope, String id, String prefix) {
		Scope lexicalScope = dyscope.lexicalScope();
		int numVars = lexicalScope.numVariables();
		BitSet reachers = dyscope.getReachers();
		int bitSetLength = reachers.length();
		boolean first = true;

		out.println(prefix + "dyscope d" + id + " (parent ID=" + dyscope.getParent() + ", static=" + lexicalScope.id()
				+ ")");
		out.print(prefix + "| reachers = {");
		for (int j = 0; j < bitSetLength; j++) {
			if (reachers.get(j)) {
				if (first)
					first = false;
				else
					out.print(",");
				out.print(j);
			}
		}
		out.println("}");
		out.println(prefix + "| variables");
		for (int i = 0; i < numVars; i++) {
			Variable variable = lexicalScope.variable(i);
			SymbolicExpression value = dyscope.getValue(i);

			out.print(prefix + "| | " + variable.name() + " = ");
			if (variable.type().isPointerType()) {
				out.println(this.pointerValueToString(value));
			} else
				out.println(value);
		}
		out.flush();
	}

	/**
	 * Obtains the string representation of a pointer value.
	 * 
	 * @param pointer
	 *            The pointer value whose string representation is to be
	 *            generated.
	 * @return The string representation of the given pointer value.s
	 */
	private String pointerValueToString(SymbolicExpression pointer) {
		StringBuffer result = new StringBuffer();

		if (pointer.operator() == SymbolicOperator.NULL)
			return pointer.toString();
		else {
			result.append('&');
			return result.toString();
		}
	}

	/* *********************** Package-private Methods ********************* */

	/**
	 * Makes this state canonic. Recursively makes the path condition, dynamic
	 * scopes, and process states canonic, then applies the flyweight pattern to
	 * this state.
	 * 
	 * @param canonicId
	 *            the canonic ID to assign to this state
	 * @param universe
	 *            the symbolic universe used to canonize symbolic expressions
	 * @param scopeMap
	 *            the map used to flyweight dynamic scopes
	 * @param processMap
	 *            the map used to flyweight process states
	 */
	void makeCanonic(AtomicInteger canonicId, SymbolicUniverse universe,
			Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap,
			Map<ImmutableProcessState, ImmutableProcessState> processMap) {
		int numProcs = processStates.length;
		int numScopes = dyscopes.length;

		pathCondition = (BooleanExpression) universe.canonic(pathCondition);
		for (int i = 0; i < numProcs; i++) {
			ImmutableProcessState processState = processStates[i];

			if (processState != null && !processState.isCanonic())
				processStates[i] = canonic(processState, processMap);
		}
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope scope = dyscopes[i];

			if (!scope.isCanonic())
				dyscopes[i] = canonic(scope, scopeMap, universe);
		}
		this.canonicId = canonicId.getAndIncrement();
	}

	/**
	 * Creates a shallow copy of the process state array with one additional
	 * null entry, and returns it.
	 * 
	 * @return an array one longer than the process state array with entry i
	 *         containing process state i for all but the last entry, which is
	 *         null
	 */
	ImmutableProcessState[] copyAndExpandProcesses() {
		ImmutableProcessState[] newProcesses = new ImmutableProcessState[processStates.length + 1];

		System.arraycopy(processStates, 0, newProcesses, 0, processStates.length);
		return newProcesses;
	}

	/**
	 * Creates a shallow copy of the dynamic scope array with one additional
	 * null entry, and returns it.
	 * 
	 * @return an array one longer than the dynamic scope array with entry i
	 *         containing dynamic scope i for all but the last entry, which is
	 *         null
	 */
	ImmutableDynamicScope[] copyAndExpandScopes() {
		ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[dyscopes.length + 1];

		System.arraycopy(dyscopes, 0, newScopes, 0, dyscopes.length);
		return newScopes;
	}

	/**
	 * Returns a shallow copy of the process state array.
	 * 
	 * @return a shallow copy of the process state array
	 */
	ImmutableProcessState[] copyProcessStates() {
		ImmutableProcessState[] newProcesses = new ImmutableProcessState[processStates.length];

		System.arraycopy(processStates, 0, newProcesses, 0, processStates.length);
		return newProcesses;
	}

	/**
	 * Returns a shallow copy of the dynamic scope array.
	 * 
	 * @return a shallow copy of the dynamic scope array
	 */
	ImmutableDynamicScope[] copyScopes() {
		ImmutableDynamicScope[] newScopes = new ImmutableDynamicScope[dyscopes.length];

		System.arraycopy(dyscopes, 0, newScopes, 0, dyscopes.length);
		return newScopes;
	}

	/**
	 * Get a new copy of the collective snapshot queues in this state. If the
	 * {@link #snapshotsQueues} field is null, return an empty HashMap.
	 * 
	 * @return
	 */
	ImmutableCollectiveSnapshotsEntry[][] getSnapshotsQueues() {
		ImmutableCollectiveSnapshotsEntry[][] returnedEntry;

		if (snapshotsQueues == null) {
			snapshotsQueues = new ImmutableCollectiveSnapshotsEntry[0][0];
			return new ImmutableCollectiveSnapshotsEntry[0][0];
		} else {
			returnedEntry = new ImmutableCollectiveSnapshotsEntry[snapshotsQueues.length][];

			for (int i = 0; i < snapshotsQueues.length; i++)
				returnedEntry[i] = snapshotsQueues[i].clone();
		}
		return returnedEntry;
	}

	/**
	 * Update the {@link #snapshotsQueues} field, return a new state with
	 * updated collective snapshot queues
	 * 
	 * @param newQueues
	 * @return
	 */
	ImmutableState setSnapshotsQueues(ImmutableCollectiveSnapshotsEntry[][] newQueues) {
		ImmutableState newState = newState(this, processStates, dyscopes, pathCondition);
		int queueLength = newQueues.length;

		newState.snapshotsQueues = newQueues.clone();
		for (int i = 0; i < queueLength; i++)
			newState.snapshotsQueues[i] = newQueues[i].clone();
		return newState;
	}

	/**
	 * Finds the dynamic scope containing the given variable. The search begins
	 * in the current dynamic scope of process pid (i.e., the dyscope at the top
	 * of that process' call stack). If the variable is not found there, it then
	 * moves to the parent dyscope, and so on. If the variable is not found
	 * after looking in the root dyscope, an exception is thrown.
	 * 
	 * @param pid
	 *            the PID of the process containing the variable
	 * @param variable
	 *            the static variable
	 * @return the "innermost" dynamic scope containing the variable
	 */
	ImmutableDynamicScope getScope(int pid, Variable variable) {
		ImmutableProcessState proc = this.getProcessState(pid);
		int numStackEntries = proc.stackSize();
		Scope variableScope = variable.scope();
		ImmutableDynamicScope scope;

		for (int i = 0; i < numStackEntries; i++) {
			int scopeId = proc.getStackEntry(i).scope();

			while (scopeId >= 0) {
				scope = getDyscope(scopeId);
				if (scope.lexicalScope() == variableScope)
					return scope;
				scopeId = getParentId(scopeId);
			}
		}
		throw new IllegalArgumentException("Variable not in scope: " + variable);
	}

	/**
	 * Is this state canonic?
	 * 
	 * @return true iff this is canonic
	 */
	boolean isCanonic() {
		return canonicId >= 0;
	}

	/**
	 * Returns a new state equivalent to this one, except that the dyscopes
	 * field is replaced with the given parameter.
	 * 
	 * @param dyscopes
	 *            new value of dyscopes array
	 * @return new state with new dyscopes
	 */
	ImmutableState setScopes(ImmutableDynamicScope[] dyscopes) {
		ImmutableState result = new ImmutableState(processStates, dyscopes, pathCondition);

		if (procHashed) {
			result.procHashed = true;
			result.procHashCode = procHashCode;
		}
		result.snapshotsQueues = this.snapshotsQueues;
		result.collectibleCounts = this.collectibleCounts;
		return result;
	}

	/**
	 * Returns a new state equivalent to this one, except that the process state
	 * of PID index is replaced with the given process state.
	 * 
	 * Precondition: index == processState.pid()
	 * 
	 * @param processState
	 *            new value for process state of PID index
	 * @param index
	 *            PID of process
	 * @return new state with new process state
	 */
	ImmutableState setProcessState(int index, ImmutableProcessState processState) {
		int n = processStates.length;
		ImmutableProcessState[] newProcessStates = new ImmutableProcessState[n];
		ImmutableState result;

		System.arraycopy(processStates, 0, newProcessStates, 0, n);
		newProcessStates[index] = processState;
		result = new ImmutableState(newProcessStates, dyscopes, pathCondition);
		if (scopeHashed) {
			result.scopeHashed = true;
			result.scopeHashCode = scopeHashCode;
		}
		result.snapshotsQueues = this.snapshotsQueues;
		result.collectibleCounts = this.collectibleCounts;
		return result;
	}

	/**
	 * Returns a new state in which the process state array field has been
	 * replaced by the given array.
	 * 
	 * @param processStates
	 *            new value for process states field
	 * @return new immutable state with process states field as given
	 */
	ImmutableState setProcessStates(ImmutableProcessState[] processStates) {
		ImmutableState result = new ImmutableState(processStates, dyscopes, pathCondition);

		if (scopeHashed) {
			result.scopeHashed = true;
			result.scopeHashCode = scopeHashCode;
		}
		result.snapshotsQueues = this.snapshotsQueues;
		result.collectibleCounts = this.collectibleCounts;
		return result;
	}

	/**
	 * Returns the corresponding snapshot queue by giving the identifier of an
	 * MPI communicator (The identifier is a component of the CIVL MPI library
	 * implementation). If there is no such a snapshot queue for the MPI
	 * communicator, returns an empty array.
	 * 
	 * @param id
	 *            The identifier of a MPI communicator
	 * @return
	 */
	ImmutableCollectiveSnapshotsEntry[] getSnapshots(int id) {
		if (snapshotsQueues == null)
			snapshotsQueues = new ImmutableCollectiveSnapshotsEntry[id + 1][0];
		if (snapshotsQueues.length > id)
			return snapshotsQueues[id].clone();
		else
			return new ImmutableCollectiveSnapshotsEntry[0];
	}

	/**
	 * Update one collective snapshot queue. Returns a new state after the
	 * updating.
	 * 
	 * @param id
	 *            The identifier of an MPI communicator which specifies the
	 *            updated snapshot queue
	 * @param queue
	 *            The updated snapshot queue
	 * @return
	 */
	ImmutableState updateQueue(int id, ImmutableCollectiveSnapshotsEntry[] queue) {
		ImmutableState newState;
		int newLength;

		assert queue != null;
		newState = newState(this, processStates, dyscopes, pathCondition);
		if (newState.snapshotsQueues.length <= id)
			newState.snapshotsQueues = new ImmutableCollectiveSnapshotsEntry[id + 1][];
		else
			newState.snapshotsQueues = this.snapshotsQueues.clone();
		newLength = snapshotsQueues.length;
		// For unchanged queues, there is no need to do clone();
		for (int i = 0; i < newLength; i++)
			newState.snapshotsQueues[i] = this.snapshotsQueues[i];
		// The updated queue must be cloned in case it is changed some where.
		newState.snapshotsQueues[id] = queue.clone();
		return newState;
	}

	/**
	 * Updates the count of the collectible symbolic constant of the given index
	 * 
	 * @param index
	 *            the index of the count to be updated
	 * @param newCount
	 *            the new count of the given index
	 * @return the new state which is identical to this state except that the
	 *         collectible count of the given index is updated
	 */
	ImmutableState updateCollectibleCount(int index, int newCount) {
		int length = this.collectibleCounts.length;
		int[] newCollectibleCounts = new int[length];
		ImmutableState newState = newState(this, processStates, dyscopes, pathCondition);

		System.arraycopy(this.collectibleCounts, 0, newCollectibleCounts, 0, length);
		newCollectibleCounts[index] = newCount;
		newState.collectibleCounts = newCollectibleCounts;
		return newState;
	}

	/* ************************ Methods from State ************************* */

	@Override
	public int getCanonicId() {
		return canonicId;
	}

	@Override
	public int getDepth() {
		return depth;
	}

	@Override
	public int getParentId(int scopeId) {
		return getDyscope(scopeId).getParent();
	}

	@Override
	public BooleanExpression getPathCondition() {
		return pathCondition;
	}

	@Override
	public ImmutableProcessState getProcessState(int pid) {
		return processStates[pid];
	}

	@Override
	public Iterable<ProcessState> getProcessStates() {
		if (processStateIterable == null) {
			processStateIterable = new ProcessStateIterable();
		}
		return processStateIterable;
	}

	@Override
	public ImmutableDynamicScope getDyscope(int id) {
		return dyscopes[id];
	}

	@Override
	public int getDyscopeID(int pid, Variable variable) {
		Scope variableScope = variable.scope();

		if (variableScope.id() == ModelConfiguration.STATIC_CONSTANT_SCOPE) {
			return ModelConfiguration.DYNAMIC_CONSTANT_SCOPE;
		}

		int scopeId = getProcessState(pid).getDyscopeId();
		DynamicScope scope;

		while (scopeId >= 0) {
			scope = getDyscope(scopeId);
			if (scope.lexicalScope() == variableScope)
				return scopeId;
			scopeId = getParentId(scopeId);
		}
		return ModelConfiguration.DYNAMIC_REMOVED_SCOPE;
	}

	@Override
	public SymbolicExpression getVariableValue(int scopeId, int variableId) {
		DynamicScope scope = getDyscope(scopeId);

		return scope.getValue(variableId);
	}

	@Override
	public int getDyscope(int pid, Scope scope) {
		return this.getDyscope(pid, scope.id());
	}

	@Override
	public int getDyscope(int pid, int scopeID) {
		if (scopeID == ModelConfiguration.STATIC_CONSTANT_SCOPE)
			return ModelConfiguration.DYNAMIC_CONSTANT_SCOPE;

		ImmutableProcessState proc = getProcessState(pid);
		int stackSize = proc.stackSize();
		int stackIndex = 0;
		int dyScopeId = proc.getStackEntry(stackIndex).scope();
		DynamicScope dyScope = this.getDyscope(dyScopeId);

		while (dyScope.lexicalScope().id() != scopeID) {
			dyScopeId = this.getParentId(dyScopeId);
			if (dyScopeId < 0) {
				stackIndex++;
				if (stackIndex >= stackSize)
					return ModelConfiguration.DYNAMIC_REMOVED_SCOPE;
				dyScopeId = proc.getStackEntry(stackIndex).scope();
			}
			dyScope = this.getDyscope(dyScopeId);
		}
		return dyScopeId;
	}

	@Override
	public String identifier() {
		if (canonicId != -1)
			return String.valueOf(this.canonicId);
		else
			return "(" + instanceId + ")";
	}

	@Override
	public int numberOfReachers(int sid) {
		return getDyscope(sid).numberOfReachers();
	}

	@Override
	public int numProcs() {
		return processStates.length;
	}

	@Override
	public int numLiveProcs() {
		int count = 0;

		for (ProcessState procState : processStates)
			if (procState != null)
				count++;
		return count;
	}

	@Override
	public int numDyscopes() {
		return dyscopes.length;
	}

	@Override
	public boolean onStack() {
		return onStack;
	}

	@Override
	public void print(PrintStream out) {
		int numScopes = numDyscopes();
		int numProcs = numProcs();

		out.print("State " + identifier());
		out.println();
		out.println("| Path condition");
		out.println("| | " + pathCondition);
		out.println("| Dynamic scopes");
		for (int i = 0; i < numScopes; i++) {
			ImmutableDynamicScope dyscope = (ImmutableDynamicScope) dyscopes[i];

			if (dyscope == null)
				out.println("| | dyscope - (id=" + i + "): null");
			else
				this.printImmutableDynamicScope(out, dyscope, "" + i, "| | ");
		}
		out.println("| Process states");
		for (int i = 0; i < numProcs; i++) {
			ProcessState process = processStates[i];

			if (process == null)
				out.println("| | process - (id=" + i + "): null");
			else
				process.print(out, "| | ");
		}
		out.flush();
	}

	@Override
	public boolean reachableByProcess(int sid, int pid) {
		return getDyscope(sid).reachableByProcess(pid);
	}

	@Override
	public int rootDyscopeID() {
		return 0;
	}

	@Override
	public boolean seen() {
		return seen;
	}

	@Override
	public void setDepth(int value) {
		this.depth = value;
	}

	@Override
	public void setOnStack(boolean onStack) {
		this.onStack = onStack;
	}

	@Override
	public ImmutableState setPathCondition(BooleanExpression pathCondition) {
		ImmutableState result = new ImmutableState(processStates, dyscopes, pathCondition);

		if (scopeHashed) {
			result.scopeHashed = true;
			result.scopeHashCode = scopeHashCode;
		}
		if (procHashed) {
			result.procHashed = true;
			result.procHashCode = procHashCode;
		}
		result.collectibleCounts = this.collectibleCounts;
		result.snapshotsQueues = snapshotsQueues;
		return result;
	}

	@Override
	public void setSeen(boolean seen) {
		this.seen = seen;
	}

	@Override
	public SymbolicExpression valueOf(int pid, Variable variable) {
		DynamicScope scope = getScope(pid, variable);
		int variableID = scope.lexicalScope().getVid(variable);

		return scope.getValue(variableID);
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof ImmutableState) {
			ImmutableState that = (ImmutableState) object;

			if (canonicId >= 0 && that.canonicId >= 0)
				return false;
			if (hashed && that.hashed && hashCode != that.hashCode)
				return false;
			if (!pathCondition.equals(that.pathCondition))
				return false;
			if (procHashed && that.procHashed && procHashCode != that.procHashCode)
				return false;
			if (scopeHashed && that.scopeHashed && scopeHashCode != that.scopeHashCode)
				return false;
			if (!Arrays.equals(processStates, that.processStates))
				return false;
			if (!Arrays.equals(dyscopes, that.dyscopes))
				return false;
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		if (!hashed) {
			if (!procHashed) {
				procHashCode = Arrays.hashCode(processStates);
				procHashed = true;
			}
			if (!scopeHashed) {
				scopeHashCode = Arrays.hashCode(dyscopes);
				scopeHashed = true;
			}
			hashCode = pathCondition.hashCode() ^ procHashCode ^ scopeHashCode;
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		return "State " + identifier();
	}

	@Override
	public StringBuffer callStackToString() {
		StringBuffer result = new StringBuffer();
		int numProcs = this.numProcs();

		result.append("\nCall stacks:\n");
		for (int i = 0; i < numProcs; i++) {
			ProcessState process = processStates[i];

			// result.append("\n");
			if (process != null)
				result.append(process.toSBrieftringBuffer());
		}
		return result;
	}

	@Override
	public SymbolicExpression[] getOutputValues(String[] outputNames) {
		DynamicScope rootDyscope = this.dyscopes[0];
		Scope rootScope = rootDyscope.lexicalScope();
		int numOutputs = outputNames.length;
		SymbolicExpression[] outputValues = new SymbolicExpression[numOutputs];

		for (int i = 0; i < numOutputs; i++) {
			Variable outputVariable = rootScope.variable(outputNames[i]);

			outputValues[i] = rootDyscope.getValue(outputVariable.vid());
		}
		return outputValues;
	}

	@Override
	public boolean isFinalState() {
		return processStates.length == 1 && processStates[0].hasEmptyStack();
	}

	@Override
	public void setAllSuccessorsOnStack(boolean value) {
		allSuccessorsOnStack = value;
	}

	@Override
	public boolean getAllSuccessorsOnStack() {
		return allSuccessorsOnStack;
	}

	@Override
	public boolean allSuccessorsVisited() {
		return allSuccessorsVisited;
	}

	@Override
	public void setAllSuccessorsVisited(boolean value) {
		this.allSuccessorsVisited = value;
	}

}
