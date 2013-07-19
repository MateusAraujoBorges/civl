/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * A function call. Either of the form f(x) or else v=f(x).
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CallStatement extends Statement {

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	LHSExpression lhs();

	/**
	 * @return The function being called.
	 */
	Function function();

	/**
	 * @return The arguments to the function.
	 */
	Vector<Expression> arguments();

	/**
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	void setLhs(LHSExpression lhs);

	/**
	 * @param function
	 *            The function being called.
	 */
	void setFunction(Function function);

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	void setArguments(Vector<Expression> arguments);

}
