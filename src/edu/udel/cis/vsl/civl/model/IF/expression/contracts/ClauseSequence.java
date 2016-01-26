package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import java.util.Iterator;

import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A sequence of contract clauses. Usually it is used to represent a block of
 * contract clauses.
 * 
 * @author ziqing
 *
 */
public interface ClauseSequence extends Expression {
	/**
	 * Returns the iterator of this sequence of contract clauses
	 * 
	 * @return
	 */
	Iterator<ContractClause> getIterator();

	/**
	 * Casting the sequence of contracts clauses into an array of T
	 * 
	 * @param receiver
	 */
	void toArray(ContractClause[] receiver);

	/**
	 * Return the number of single contract clauses in this sequence
	 * 
	 * @return
	 */
	int length();

	@Override
	ClauseSequence replaceWith(ConditionalExpression oldExpr, Expression newExpr);
}
