package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;

/**
 * <p>
 * Updates the loop variables with the next element of a domain.
 * </p>
 * 
 * @author Manchun Zheng (zmanchun)
 */
public interface NextInDomainStatement extends Statement {

	/**
	 * Returns the iteration domain expression, which is the expression
	 * following the colon.
	 * 
	 * @return the iteration domain expression
	 */
	Expression domain();

	/**
	 * Returns the list of loop variables, ordered from left to right.
	 * 
	 * @return the list of loop variables
	 */
	List<VariableExpression> loopVariables();
}