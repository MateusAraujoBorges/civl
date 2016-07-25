package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A Library Executor provides the semantics for system functions defined in a
 * library. It provides a method to "execute" each system library function.A new
 * library is implemented in the package named as
 * "edu.udel.cis.vsl.civl.library." ( {@link CommonLibraryLoader#CLASS_PREFIX})
 * + library name. And the class name of the executor is: "Lib" + library name +
 * "Enabler". For example, the stdio library executor is implemented as the
 * class edu.udel.cis.vsl.civl.library.stdio.LibstdioExecutor.
 * 
 */
public interface LibraryExecutor {

	/**
	 * <p>
	 * Executes the given call statement for a certain process at the given
	 * state.
	 * </p>
	 * <p>
	 * Precondition: the given call statement is enabled for the process with
	 * the given pid, and the function of the call statement is provided by this
	 * library.
	 * </p>
	 * 
	 * @param state
	 *            The state where the call statement is to be executed.
	 * @param pid
	 *            The PID of the process that the statement belongs to.
	 * @param statement
	 *            The call statement to be executed.
	 * @param functionName
	 *            The name of the system function that this call is going to
	 *            executed. Note: we need this when the function of the call
	 *            statement is a function pointer.
	 * @return The resulting state after executing the call statement, plus the
	 *         return value of the function call, which is NULL if the function
	 *         returns void.
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException;

	/**
	 * Executes a certain system function with the given list of argument
	 * values, which allows the evaluation of the arguments and the execution of
	 * the body to happen at different states.
	 * 
	 * @param state
	 *            the state to used for executing the function body
	 * @param pid
	 *            the PID of the process that triggers this execution
	 * @param call
	 *            the call statement
	 * @param functionName
	 *            The name of the system function that this call is going to
	 *            executed. Note: we need this when the function of the call
	 *            statement is a function pointer.
	 * @param argumentValues
	 *            the values of the arguments, which are the result of
	 *            evaluating the list of arguments of the given call statement
	 *            at some state, which may or may not be the same as the state
	 *            to execute the function body
	 * @return the state after executing the system function call at the given
	 *         state
	 * @throws UnsatisfiablePathConditionException
	 */
	State executeWithValue(State state, int pid, CallOrSpawnStatement call,
			String functionName, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException;

}
