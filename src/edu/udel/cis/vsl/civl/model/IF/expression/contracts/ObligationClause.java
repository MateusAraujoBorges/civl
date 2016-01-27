package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * <p>
 * This class represents a series of contract clauses. They are called
 * obligation contract clauses here because they are a group of very basic
 * clauses that stands for the obligations that must be delivered by either
 * caller or callee of a function.
 * </p>
 * 
 * <p>
 * Obligation contract clauses consist of requirements, assurance and
 * assumptions. All three of them have the same notation:
 * <code>[clause_kind]  [predicate];</code> where<br>
 * <code>[clause_kind] ::= requires | ensures | assumes </code> and <br>
 * <code>[predicate] ::= boolean expression </code>
 * </p>
 * 
 * 
 * @author ziqing
 *
 */
public interface ObligationClause extends Expression, ContractClause {
	/**
	 * Returns the body expression of this contract clause. The returned body
	 * expression is an boolean predicate.
	 * 
	 * @return
	 */
	Expression getBody();
}
