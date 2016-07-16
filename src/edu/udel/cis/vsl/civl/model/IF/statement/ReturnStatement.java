/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A return statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ReturnStatement extends Statement {

	/**
	 * @return The expression being returned. Null if non-existent.
	 */
	Expression expression();

	/**
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	void setExpression(Expression expression);

	/**
	 * @return True if and only if this is the return statement that belongs to
	 *         a "Run" function.
	 */
	boolean fromRunProcFunction();

	/**
	 * Set this ReturnStatement as it belongs to a "Run" function. A Run
	 * function is the function translated from a run statement.
	 * 
	 * @param fromRunProcFunc
	 *            True to set this ReturnStatement as it belongs to a "Run"
	 *            function.
	 */
	void setFromRunProcFunction(boolean fromRunProcFunc);

}
