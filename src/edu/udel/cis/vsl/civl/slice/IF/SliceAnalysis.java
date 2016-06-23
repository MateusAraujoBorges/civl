package edu.udel.cis.vsl.civl.slice.IF;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * Given an error trace, this analysis computes
 * the symbolic variables and the branches taken
 * that were involved in reaching the error. If
 * a the branch choice is independent of reaching
 * the error, then this branch is "sliced" away,
 * i.e. ignored.  
 * 
 * For example, if the path
 * condition includes the clause (X < 0), but the
 * analysis determines that both (X < 0) and 
 * !(X < 0) can lead to the error, then the branch
 * (X < 0) is sliced away.
 * 
 * @author mgerrard
 *
 */

public interface SliceAnalysis {
	/*
	 * A mapping from a SymbolicExpression to the
	 * string made up of: the line number and syntactic
	 * name of the LHS in a read() assignment.
	 */
	public Set<Pair<SymbolicExpression,String>> inputSymbolicExprs();

	/*
	 * 1st elem : input variables
	 * 2nd elem : branches involved in error
	 * 3rd elem : branches-in-question
	 */
	public List<Set<String>> expectedOutput();

}
