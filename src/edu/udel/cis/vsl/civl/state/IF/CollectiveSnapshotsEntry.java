package edu.udel.cis.vsl.civl.state.IF;

import java.util.Iterator;

import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableCollectiveSnapshotsEntry;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableMonoState;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class represents one complete entry for the snapshots queue used in
 * collective assertion checking.
 * 
 * Once a entry created, it stores the information of the communicator and
 * corresponds to the communicator.
 * 
 * Every process will add themselves into one entry once they reach the
 * corresponding "collective assertion".
 * 
 * @author ziqing
 *
 */
public interface CollectiveSnapshotsEntry {

	/**
	 * The {@link ContractClauseKind} associates to this entry
	 * 
	 * @return
	 */
	ContractKind contractKind();

	/**
	 * If the entry is complete and can be dequeue for evaluation
	 * 
	 * @return
	 */
	boolean isComplete();

	/**
	 * If the process is recorded.
	 * 
	 * @param place
	 * @return
	 */
	boolean isRecorded(int place);

	/**
	 * Returns the number of {@link ImmutableMonoState} in this entry
	 * 
	 * @return
	 */
	int numMonoStates();

	/**
	 * Returns the identifier of this entry
	 * 
	 * @return
	 */
	int identifier();

	/**
	 * Returns the number of processes involved in this entry
	 * 
	 * @return
	 */
	int numInvolvedProcesses();

	/**
	 * Returns the message channels stored in this entry.
	 * 
	 *
	 * @return An array of length 2 of message buffers. one for "p2p" and the
	 *         other for "col"
	 */
	SymbolicExpression getMsgBuffers();

	/**
	 * Returns all stored assertion predicates (one for each process) in this
	 * entry.
	 * 
	 * @return
	 */
	Expression[] getAllAssertions();

	/**
	 * Insert a new {@link ImmutableMonoState} belonging to a DIFFERENT (if the
	 * process is existed, an error will be reported) process. Returns the
	 * number of the stored {@link ImmutableMonoState} after the insertion. If
	 * the insertion completes the entry, it changes the result which will be
	 * returned by {@link #isComplete()}.
	 * 
	 * @precondition The PID of the MonoState must be in
	 *               {@link #involvedProcesses()} and never be recorded i.e.
	 *               {@link #isRecorded(PID)} returns false and
	 *               {@link #isComplete()} returns false.
	 * @param monoState
	 * @return
	 */
	ImmutableCollectiveSnapshotsEntry insertMonoState(int place,
			ImmutableMonoState monoState, Expression assertion);

	/**
	 * *
	 * <p>
	 * <b>Pre-condition:</b> The given variable must be saved in this collective
	 * entry.
	 * </p>
	 * <p>
	 * Returns saved value for the given variable (which is represented with a
	 * pair of variable id and lexical scope id).
	 * </p>
	 * 
	 * @param var
	 *            an variable represented by a pair of variable id and lexical
	 *            scope id
	 * @return
	 */
	Iterator<Pair<int[], SymbolicExpression>> agreedValueIterator();

	/**
	 * <p>
	 * <b>Pre-condition:</b><code>vars.length == values.length</code>
	 * <code>forall i : [0, vars.length) ==> evaluation(vars[i]) == values[i];</code>
	 * </p>
	 * <p>
	 * <b>Summary: </b> Saves a set of variables and their values into the
	 * collective entry.
	 * </p>
	 * 
	 * @param vars
	 *            The type should in face be int[][2]. It represents an array of
	 *            pairs of ints, each pair is an variable id and a lexical scope
	 *            id.
	 * @param values
	 *            An array of values. One for each variable.
	 * @return
	 */
	ImmutableCollectiveSnapshotsEntry deliverAgreedVariables(int[][] vars,
			SymbolicExpression[] values);
}
