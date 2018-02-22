package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An ACSL predicate. See ACSL: ANSI/ISO C Specification Language v1.12 secction
 * 2.6.1.
 * 
 * <p>
 * An ACSL predicate in CIVL model is a boolean type function which is
 * guaranteed to be side-effect free since one cannot write an ACSL predicate
 * with side-effects.
 * </p>
 * 
 * @author ziqing
 *
 */
public interface ACSLPredicate extends CIVLFunction {
	/**
	 * @return the definition of an ACSL predicate, which is an boolean
	 *         expression. Since no one can write side-effect expressions using
	 *         ACSL constructs, the expression is guaranteed side-effect free.
	 */
	Expression definition();
}
