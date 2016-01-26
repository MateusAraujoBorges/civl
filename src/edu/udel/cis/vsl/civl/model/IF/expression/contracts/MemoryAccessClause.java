package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This class represents contract clauses stating properties of accessing memory
 * locations. e.g. read/write on specific memory locations
 * 
 * @author ziqing
 *
 */
public interface MemoryAccessClause extends ContractClause {
	// TODO: Giving multiple interfaces because we are considering there might
	// be some other constructors will be added as MemoryAccessClauses.
	/**
	 * Returns true if and only if this object represents an "\assigns" clause.
	 * 
	 * @return
	 */
	boolean isAssigns();

	/**
	 * Returns true if and only if this object represents a "\reads" clause.
	 * 
	 * @return
	 */
	boolean isReads();

	/**
	 * Returns all memory locations specified by this clause
	 */
	Expression[] memoryLocations();
}
