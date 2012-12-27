/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.statement.Statement;
import edu.udel.cis.vsl.sarl.symbolic.IF.SymbolicExpressionIF;

/**
 * A choose transition represents one of the outgoing transitions from a choose
 * statement. There is one such transition for each value that can result from
 * the choose.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class ChooseTransition extends SimpleTransition {

	private SymbolicExpressionIF value;
	
	/**
	 * A choose transition represents one of the outgoing transitions from a
	 * choose statement. There is one such transition for each value that can
	 * result from the choose.
	 * 
	 * @param pathCondition
	 *            The path condition that should result after executing the
	 *            transition.
	 * @param pid
	 *            The process id of the process executing this transition.
	 * @param statement
	 *            The statement corresponding to this transition.
	 * @param value
	 *            The value resulting from the choose for this transition.
	 */
	public ChooseTransition(SymbolicExpressionIF pathCondition, int pid,
			Statement statement, SymbolicExpressionIF value) {
		super(pathCondition, pid, statement);
		this.value = value;
	}

	/**
	 * The value resulting from the choose for this transition.
	 */
	public SymbolicExpressionIF value() {
		return value;
	}
}
