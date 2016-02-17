package edu.udel.cis.vsl.civl.model.IF.contract;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.model.IF.Sourceable;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This represents a block of ACSL contract for a function.
 * 
 * @author Manchun Zheng
 *
 */
public interface FunctionContract extends Sourceable {

	/**
	 * Returns the default behavior of the function.
	 * 
	 * @return
	 */
	FunctionBehavior defaultBehavior();

	/**
	 * Returns the named behaviors of the function.
	 * 
	 * @return
	 */
	Iterable<NamedFunctionBehavior> namedBehaviors();

	/**
	 * Returns the guard of the function.
	 * 
	 * @return
	 */
	Expression guard();

	/**
	 * Does the contract contains <code>pure</code> clause?
	 * 
	 * @return
	 */
	boolean isPure();

	/**
	 * Updates the contract to denote if it contains <code>pure</code> clause.
	 * 
	 * @param value
	 */
	void setPure(boolean value);

	/**
	 * Sets the guard of the function.
	 * 
	 * @param expression
	 */
	void setGuard(Expression expression);

	/**
	 * Sets the default behavior of the function.
	 * 
	 * @param behavior
	 */
	void setDefaultBehavior(FunctionBehavior behavior);

	/**
	 * Adds a named behavior to the function.
	 * 
	 * @param behavior
	 */
	void addNamedBehavior(NamedFunctionBehavior behavior);

	/**
	 * returns the behavior with the given name; null if no such behavior
	 * exists.
	 * 
	 * @param name
	 * @return
	 */
	NamedFunctionBehavior getBehavior(String name);

	/**
	 * prints this function contract
	 * 
	 * @param prefix
	 * @param out
	 * @param isDebug
	 */
	void print(String prefix, PrintStream out, boolean isDebug);
}
