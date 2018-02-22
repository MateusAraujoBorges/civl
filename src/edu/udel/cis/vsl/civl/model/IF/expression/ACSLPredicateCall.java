package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.ACSLPredicate;

/**
 * An ACSL predicate call likes a function call but the function is guaranteed
 * to be a pure mathematical function (side-effect free, since one cannot write
 * predicates with side effects in ACSL annotation).
 * 
 * @author ziqing
 *
 */
public interface ACSLPredicateCall extends Expression {
	/**
	 * @return The {@link ACSLPredicate} that is called
	 */
	ACSLPredicate predicate();

	/**
	 * @return The actual arguments of the predicate call
	 */
	Expression[] actualArguments();
}
