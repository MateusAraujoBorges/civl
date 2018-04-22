package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * <p>
 * A logic function is a function whose definition (body) is either absent (i.e.
 * uninterpreted) or a side-effect free expression.
 * </p>
 * 
 * <p>
 * A function call to a logic function <code>f(formal-param)</code> will be
 * evaluated to <code>f(actual-param)</code>. The function will be interpreted ,
 * if it has a definition, when a formula is sent to theorem provers. Inlining
 * the function definition is possible but currently not supported.
 * </p>
 * 
 * <p>
 * A set of axioms can be define over a logic function which come up a "theory".
 * Theorem provers will have the knowledge about theories whenever they are
 * called.
 * </p>
 * 
 * <p>
 * A call to a logic function is side-effect free as well hence login function
 * can be recursively defined. To keep logic function calls side-effect free,
 * function pointers are not allowed to refer to logic functions.
 * </p>
 * 
 * @author ziqing
 *
 */
public interface LogicFunction extends CIVLFunction {
	/**
	 * @return the definition of a logic function. Optional. If a logic function
	 *         has no definition, this method returns null.
	 */
	Expression definition();
}
