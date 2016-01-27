package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This class represents a series of contract clauses that claims how the
 * function will access memory locations. The notation is :
 * <code>[clause_kind] [location set]</code> where <br>
 * <code>clause_kind ::= reads | assigns </code> and <br>
 * <code>location set ::= a set of lvalues separated by commas </code>
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
