package edu.udel.cis.vsl.civl.state.common.immutable;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.state.IF.CollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class ImmutableCollectiveSnapshotsEntry implements CollectiveSnapshotsEntry {
	/**
	 * Static instance identifier
	 */
	private static int instanceId = 0;
	/**
	 * The array stores {@link ImmutableMonoState}
	 */
	private ImmutableMonoState[] monoStates;

	/**
	 * The number of inserted {@link ImmutableMonoState}
	 */
	private int numMonoStates;
	/**
	 * The array stores assertion predicates for each process
	 */
	private Expression[] predicates;

	/**
	 * Indicating if the entry is complete and can be dequeue.
	 */
	private boolean isComplete;

	private boolean[] isRecorded;

	/**
	 * Identifier of this entry
	 */
	private final int identifier = ++instanceId;

	/**
	 * The total number of processes involved in the corresponding
	 * {@link ImmutableState};
	 */
	private int numProcesses;

	private int maxPid;

	/**
	 * The {@link ContractKind} of this entry
	 */
	private ContractKind kind;

	/**
	 * Communicator channels, coordinated by source then destination.
	 */
	private SymbolicExpression channels;

	/**
	 * A pick up station is a data structure that let processes who have some
	 * same variables at a set of locations that being assigned with same values
	 * at those locations.
	 */
	/**
	 * An array of variables, a component of the pick up station.
	 */
	private int[][] pickUpVariableStation;

	/**
	 * An array of values, a component of the pick up station.
	 */
	private SymbolicExpression[] pickUpValueStation;

	private Map<int[], SymbolicExpression> loopWriteVariableSet;

	private SymbolicUniverse universe;

	/* *********************** Constructor ************************* */
	/**
	 * Create a {@link ImmutableCollectiveSnapshotsEnrty} which stores snapshots
	 * for one collective assertion. One
	 * {@link ImmutableCollectiveSnapshotsEnrty} should be correspond to one
	 * {@link ImmutableState}.
	 * 
	 * @param involvedProcesses
	 *            The PIDs of processes involved in the collective assertion,
	 *            such a information are always provided by an argument of the
	 *            collective assertion such as a MPI communicator.
	 * @param processesInState
	 *            Total number of processes in the corresponding state
	 * @param identifier
	 * @param channels
	 *            The messages channels in communicator
	 */
	ImmutableCollectiveSnapshotsEntry(int numProcesses, SymbolicUniverse universe) {
		this.numProcesses = numProcesses;
		this.isComplete = false;
		this.numMonoStates = 0;
		this.monoStates = new ImmutableMonoState[numProcesses];
		this.predicates = new Expression[numProcesses];
		this.isRecorded = new boolean[numProcesses];
		for (int i = 0; i < numProcesses; i++) {
			this.isRecorded[i] = false;
		}
		this.universe = universe;
		this.maxPid = 0;
		this.kind = null;
		this.pickUpValueStation = null;
		this.pickUpVariableStation = null;
	}

	ImmutableCollectiveSnapshotsEntry(int numProcesses, SymbolicUniverse universe, ContractKind kind) {
		this.numProcesses = numProcesses;
		this.isComplete = false;
		this.numMonoStates = 0;
		this.monoStates = new ImmutableMonoState[numProcesses];
		this.predicates = new Expression[numProcesses];
		this.isRecorded = new boolean[numProcesses];
		for (int i = 0; i < numProcesses; i++) {
			this.isRecorded[i] = false;
		}
		this.universe = universe;
		this.maxPid = 0;
		this.kind = kind;
		this.pickUpValueStation = null;
		this.pickUpVariableStation = null;
	}

	public ImmutableCollectiveSnapshotsEntry copy() {
		ImmutableCollectiveSnapshotsEntry clone = new ImmutableCollectiveSnapshotsEntry(this.numProcesses, universe);
		clone.isComplete = isComplete;
		clone.numMonoStates = numMonoStates;
		clone.monoStates = monoStates.clone();
		clone.predicates = predicates.clone();
		clone.isRecorded = this.isRecorded.clone();
		clone.maxPid = this.maxPid;
		clone.channels = channels;
		clone.kind = this.kind;
		clone.pickUpVariableStation = pickUpVariableStation;
		clone.pickUpValueStation = pickUpValueStation;
		return clone;
	}

	/* *********************** Public Methods ************************* */
	@Override
	public boolean isComplete() {
		return isComplete;
	}

	@Override
	public int numMonoStates() {
		return numMonoStates;
	}

	@Override
	public int identifier() {
		return identifier;
	}

	@Override
	public int numInvolvedProcesses() {
		return this.numProcesses;
	}

	@Override
	public Expression[] getAllAssertions() {
		return predicates;
	}

	@Override
	public SymbolicExpression getMsgBuffers() {
		return channels;
	}

	@Override
	public boolean isRecorded(int place) {
		if (place < isRecorded.length && place >= 0)
			return isRecorded[place];
		else
			return false;
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry insertMonoState(int place, ImmutableMonoState monoState,
			Expression assertion) {
		ImmutableCollectiveSnapshotsEntry newEntry;
		int pid = monoState.getProcessState().getPid();

		assert !isComplete;
		newEntry = this.copy();
		newEntry.monoStates[place] = monoState;
		newEntry.predicates[place] = assertion;
		newEntry.numMonoStates++;
		newEntry.isRecorded[place] = true;
		newEntry.kind = kind;
		if (pid >= newEntry.maxPid)
			newEntry.maxPid = pid;
		// If all snapshots are taken, check if they are coming from the correct
		// processes set.
		if (newEntry.numMonoStates == newEntry.numProcesses)
			newEntry.isComplete = true;
		return newEntry;
	}

	// TODO: why max pid ?
	public int getMaxPid() {
		return this.maxPid;
	}

	/*
	 * ************* Simplification and collection interfaces ****************
	 */
	void makeCanonic(int canonicId, Map<ImmutableDynamicScope, ImmutableDynamicScope> scopeMap,
			Map<ImmutableProcessState, ImmutableProcessState> processesMap) {
		if (monoStates == null)
			return;
		for (ImmutableMonoState state : monoStates)
			if (state != null)
				state.makeCanonic(canonicId, universe, scopeMap, processesMap);
		channels = (channels != null) ? universe.canonic(channels) : null;
		if (pickUpValueStation != null) {
			assert pickUpVariableStation != null;
			for (int i = 0; i < pickUpValueStation.length; i++)
				pickUpValueStation[i] = universe.canonic(pickUpValueStation[i]);
		}
	}

	ImmutableCollectiveSnapshotsEntry simplify(State state) {
		ImmutableMonoState[] newMonoStates;
		ImmutableCollectiveSnapshotsEntry newCollectiveEntry;
		BooleanExpression newPathCondition;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());

		newMonoStates = this.monoStates.clone();
		for (int place = 0; place < this.numProcesses; place++) {
			if (isRecorded[place]) {
				ImmutableMonoState monoState = monoStates[place];
				ImmutableDynamicScope[] newScopes;
				int numDyscopes = monoState.numDyscopes();

				newScopes = new ImmutableDynamicScope[numDyscopes];
				for (int sid = 0; sid < numDyscopes; sid++) {
					ImmutableDynamicScope oldDyscope = monoState.getDyscope(sid);
					ImmutableDynamicScope newDyscope;
					int numVars = oldDyscope.numberOfVariables();
					SymbolicExpression[] newVarValues = new SymbolicExpression[numVars];

					for (int vid = 0; vid < numVars; vid++) {
						SymbolicExpression oldValue = oldDyscope.getValue(vid);
						SymbolicExpression newValue = reasoner.simplify(oldValue);

						newVarValues[vid] = newValue;
					}
					newDyscope = oldDyscope.setVariableValues(newVarValues);
					newScopes[sid] = newDyscope;
				}
				newMonoStates[place] = monoState.setDyscopes(newScopes);
				newPathCondition = reasoner.simplify(state.getPathCondition());
				if (newPathCondition != monoState.getPathCondition()) {
					newMonoStates[place] = newMonoStates[place].setPathCondition(newPathCondition);
				}
			}
		}
		newCollectiveEntry = copy();
		// Simplify pick up station, simplification may modifies the pick up
		// station, so it has to do physical copy:
		Pair<int[][], SymbolicExpression[]> agreedVarsCopy = copyPickUpStations(pickUpVariableStation,
				pickUpValueStation);
		newCollectiveEntry.pickUpVariableStation = agreedVarsCopy.left;
		newCollectiveEntry.pickUpValueStation = agreedVarsCopy.right;
		for (int i = 0; i < pickUpValueStation.length; i++)
			newCollectiveEntry.pickUpValueStation[i] = reasoner.simplify(newCollectiveEntry.pickUpValueStation[i]);
		// Map.doc: changes on the values collection will reflect to the Map:
		if (loopWriteVariableSet != null)
			for (SymbolicExpression value : loopWriteVariableSet.values())
				value = reasoner.simplify(value);
		newCollectiveEntry.monoStates = newMonoStates;
		return newCollectiveEntry;
	}

	ImmutableMonoState[] getMonoStates() {
		return this.monoStates;
	}

	@Override
	public ContractKind contractKind() {
		return kind;
	}

	@Override
	public String toString() {
		return "Snapshot entry: " + identifier;
	}

	ImmutableCollectiveSnapshotsEntry setMsgBuffers(SymbolicExpression channels) {
		ImmutableCollectiveSnapshotsEntry newEntry = this.copy();

		newEntry.channels = (channels != null) ? universe.canonic(channels) : null;
		return newEntry;
	}

	ImmutableCollectiveSnapshotsEntry setKind(ContractKind kind) {
		ImmutableCollectiveSnapshotsEntry newEntry = this.copy();

		newEntry.kind = kind;
		return newEntry;
	}

	@Override
	public Iterator<Pair<int[], SymbolicExpression>> agreedValueIterator() {
		Pair<int[][], SymbolicExpression[]> copiedAgreedVars;

		// In case the caller modifies those agreed variables, do a physical
		// copy on them before return:
		copiedAgreedVars = copyPickUpStations(pickUpVariableStation, pickUpValueStation);
		return new Iterator<Pair<int[], SymbolicExpression>>() {
			/**
			 * Copy of variables.
			 */
			private int[][] variables = copiedAgreedVars.left;
			/**
			 * Copy of values of variables.
			 */
			private SymbolicExpression[] values = copiedAgreedVars.right;

			/**
			 * Iterative pointer
			 */
			private int pointer = 0;

			@Override
			public boolean hasNext() {
				return pointer < variables.length;
			}

			@Override
			public Pair<int[], SymbolicExpression> next() {
				Pair<int[], SymbolicExpression> result = new Pair<>(variables[pointer], values[pointer]);

				pointer++;
				return result;
			}
		};
	}

	@Override
	public ImmutableCollectiveSnapshotsEntry deliverAgreedVariables(int[][] vars, SymbolicExpression values[]) {
		assert vars.length == values.length;
		ImmutableCollectiveSnapshotsEntry clone = copy();
		Pair<int[][], SymbolicExpression[]> agreedVarsCopy;

		// Those agreed variables are changed, do physical copy on them:
		agreedVarsCopy = copyPickUpStations(vars, values);
		clone.pickUpVariableStation = agreedVarsCopy.left;
		clone.pickUpValueStation = agreedVarsCopy.right;
		return clone;
	}

	/**
	 * <p>
	 * <b>Summary: </b>Do a physical copy on the two arrays,
	 * {@link #pickUpValueStation} and {@link #pickUpVariableStation}
	 * </p>
	 * This copy is not used by {@link #copy()} because as long as these fields
	 * are not changed, not physical copy requires.
	 * 
	 * @return
	 */
	private Pair<int[][], SymbolicExpression[]> copyPickUpStations(int[][] originVars,
			SymbolicExpression[] originValues) {
		int[][] varsCopy;
		SymbolicExpression[] valuesCopy;

		if (originVars == null) {
			assert originValues == null;
			varsCopy = new int[0][2];
			valuesCopy = new SymbolicExpression[0];
		} else {
			int length = originValues.length;
			assert originVars.length == length;

			varsCopy = new int[length][2];
			for (int i = 0; i < length; i++)
				varsCopy[i] = originVars[i].clone();
			valuesCopy = originValues.clone();
		}
		return new Pair<>(varsCopy, valuesCopy);
	}

	@Override
	public Map<int[], SymbolicExpression> getLoopWriteSet() {
		assert kind == ContractKind.LOOP;
		return loopWriteVariableSet == null ? new HashMap<>() : loopWriteVariableSet;
	}

	@Override
	public void add2LoopWriteSet(int[] writtenVariable, SymbolicExpression value) {
		assert kind == ContractKind.LOOP;
		if (loopWriteVariableSet == null)
			loopWriteVariableSet = new HashMap<>();
		loopWriteVariableSet.put(writtenVariable, value);
	}

	@Override
	public void setLoopWriteSet(Map<int[], SymbolicExpression> writeSet) {
		assert kind == ContractKind.LOOP;
		loopWriteVariableSet = writeSet;
	}
}
