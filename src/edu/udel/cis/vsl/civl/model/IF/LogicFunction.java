package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.prove.IF.ProverFunctionInterpretation;

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

	static String heapVariableName(Variable formal) {
		return "_hp_" + formal.name().name();
	}

	/**
	 * @return the definition of a logic function. Optional. If a logic function
	 *         has no definition, this method returns null.
	 */
	Expression definition();

	/**
	 * <p>
	 * Caching the evaluation of a logic function since the definition of a
	 * logic function is suppose to be stateless, there is no need to repeatedly
	 * evaluate it.
	 * </p>
	 * 
	 * @param constantValue
	 *            an instance of {@linkplain ProverFunctionInterpretation}.
	 */
	void setConstantValue(ProverFunctionInterpretation constantValue);

	/**
	 * @return the cached evaluation of this logic function, which is an
	 *         instance of {@link ProverFunctionInterpretation}.
	 *         <p>
	 *         Pointer type formal parameters will be replaced with array type
	 *         symbolic constants to achieve the statelessness.
	 *         </p>
	 */
	ProverFunctionInterpretation getConstantValue();

	/**
	 * @return a map which maps indices of pointer-type formal parameters to
	 *         variable IDs of their dummy heap in the same parameter scope.
	 *         Logic function is state-independent, but the pointer-type formal
	 *         parameters must point to a some array, CIVL model allocates some
	 *         spot in the parameter scope for these pointers to point to.
	 */
	int[] pointerToHeapVidMap();
}
