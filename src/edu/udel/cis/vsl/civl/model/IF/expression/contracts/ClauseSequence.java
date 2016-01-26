package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import java.util.Iterator;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A sequence of contract clauses. Usually it is used to represent a block of
 * contract clauses.
 * 
 * @author ziqing
 *
 * @param <T>
 */
public interface ClauseSequence<T extends ContractClause> extends Expression {
	/**
	 * Returns the iterator of this sequence of contract clauses
	 * 
	 * @return
	 */
	Iterator<T> getIterator();

	/**
	 * Casting the sequence of contracts clauses into an array of T
	 * 
	 * @param receiver
	 */
	void toArray(T[] receiver);
}
