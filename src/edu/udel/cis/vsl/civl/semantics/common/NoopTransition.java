package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * A noop transition which represents a kind of transitions that have no
 * statement needs to be executed.
 * 
 * @author ziqingluo
 *
 */
public class NoopTransition extends CommonTransition implements Transition {

	public NoopTransition(BooleanExpression pathCondition, int pid,
			BooleanExpression assumption, Statement statement,
			boolean symplifyState, AtomicLockAction atomicLockAction) {
		super(pathCondition, pid, statement, symplifyState, atomicLockAction);
	}

	@Override
	public TransitionKind transitionKind() {
		return TransitionKind.NOOP;
	}
}
