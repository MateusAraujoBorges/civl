package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface MemoryUnitExpressionEvaluator {
	MemoryUnitSet evaluates(State state, int pid, MemoryUnitExpression memUnit,
			MemoryUnitSet muSet) throws UnsatisfiablePathConditionException;

	/**
	 * Evaluates the memory unit represented by an expression. A memory unit
	 * expression should be side-effect free.
	 * 
	 * @param state
	 * @param pid
	 * @param muExpr
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	MemoryUnitSet evaluateMemoryUnit(State state,
			Pair<Scope, SymbolicExpression[]> parameterScope, int pid,
			Expression muExpr) throws UnsatisfiablePathConditionException;
}
