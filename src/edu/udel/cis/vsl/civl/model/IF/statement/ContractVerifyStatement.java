package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;

/**
 * A <code>$contractVerify func(...)</code> statement which triggers modular
 * verification on the attached function "func" with given parameters.
 * 
 * @author ziqingluo
 *
 */
public interface ContractVerifyStatement extends Statement {

	/**
	 * TODO: get rid of it
	 * 
	 * @return The function being called.
	 */
	CIVLFunction function();

	/**
	 * @return The arguments to the function.
	 */
	List<Expression> arguments();

	/**
	 * TODO: get rid of this, but updates the function expression instead.
	 * 
	 * @param function
	 *            The function being called.
	 */
	void setFunction(FunctionIdentifierExpression function);

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	void setArguments(List<Expression> arguments);

	/**
	 * Check if the statement is calling a system function.
	 * 
	 * @return
	 */
	boolean isSystemCall();

	/**
	 * Denotes that this statement is a worker statement. A worker statement
	 * won't be processed by enabler
	 */
	void setAsWorker();

	/**
	 * Returns true if and only if this statement is a worker statement. A
	 * worker statement won't be processed by enabler
	 * 
	 * @return
	 */
	boolean isWorker();

	FunctionIdentifierExpression functionExpression();
}
