package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ExtendedQuantifiedExpressionNode.ExtendedQuantifier;

public interface ExtendedQuantifiedExpression extends Expression {
	/**
	 * returns the quantifier of this expression
	 * 
	 * @return
	 */
	ExtendedQuantifier extendedQuantifier();

	/**
	 * returns the lower bound
	 * 
	 * @return
	 */
	Expression lower();

	/**
	 * returns the higher bound
	 * 
	 * @return
	 */
	Expression higher();

	/**
	 * returns the function
	 * 
	 * @return
	 */
	Expression function();
}
