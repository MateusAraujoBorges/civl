package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * A ContractedFunctionCallStatement is a function call on a contracted
 * non-system function. It only be significant in Contracts System mode. This
 * statement has two kinds:
 * <ul>
 * <li>CONTRACTED_FUNCTION_ENTER: Entering a contracted function call. Executing
 * this kind of statement is mainly checking if requirements are satisfied.</li>
 * <li>CONTRACTED_FUNCTION_EXIT: Exiting a contracted function all. Executing
 * this kind of statement is mainly inferring ensurances and doing
 * synchronizations.</li>
 * </ul>
 * 
 * @author ziqingluo
 *
 */
public interface ContractedFunctionCallStatement extends Statement {
	public static enum CONTRACTED_FUNCTION_CALL_KIND {
		ENTER, EXIT
	}

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	LHSExpression lhs();

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
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	void setLhs(LHSExpression lhs);

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
	 * Returns the {@link CONTRACTED_FUNCTION_CALL_KIND}.
	 * 
	 * @return
	 */
	CONTRACTED_FUNCTION_CALL_KIND getContractedFunctionCallKind();

	Expression functionExpression();
}
