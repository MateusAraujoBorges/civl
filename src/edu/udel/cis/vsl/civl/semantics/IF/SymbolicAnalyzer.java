package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class provides methods dealing with symbolic expressions and states,
 * which represent some common-used operations like obtaining a sub-array from a
 * given array, etc.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface SymbolicAnalyzer {

	/**
	 * Casting an array to a new array with the given array type.<br>
	 * 
	 * Pre-Condition: <br>
	 * 1. The old array should be a complete array (or a object is allowed).<br>
	 * 
	 * 2. The cast should be a legal cast. <br>
	 * 
	 * 
	 * Special cases:<br>
	 * If the array(the "oldArray") is not an array type, return the object (the
	 * "oldArray") immediately.<br>
	 * If the given type is not an array type( but the "oldArray" is an array
	 * type), the length of the "oldArray" must be one, then return the first
	 * element of the "oldArray". Else, return null<br>
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param oldArray
	 *            The array needs being casted.
	 * @param type
	 *            The given type that the "oldArray" will try to cast to.
	 * @param civlsource
	 *            The CIVL source of the given array.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	SymbolicExpression arrayCasting(State state, String process,
			SymbolicExpression array, SymbolicType type, CIVLSource civlsource)
			throws UnsatisfiablePathConditionException;

	/**
	 * Flatten a given array to a ordered list of elements of that array(Here
	 * element should never be array type any more). <br>
	 * 
	 * e.g. 1 For an array <code>int a[2][2] = {1,2,3,4}</code>, the unrolled
	 * list will be <code>{1,2,3,4}</code>
	 * 
	 * e.g. 2. Given a variable <code> int a = 1;</code>, this function will
	 * give you an unrolled list <code>{1}</code>.
	 * 
	 * @author Ziqing Luo
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param array
	 *            The given array.(Or can be a single object, but by intention,
	 *            this function is mainly for multi-dimensional arrays)
	 * @param civlsource
	 *            The CIVL source of the given array.
	 * @return
	 */
	SymbolicExpression arrayFlatten(State state, String process,
			SymbolicExpression array, CIVLSource civlsource);

	/**
	 * Similar function to @link{arrayFlatten} with the @link{java.util.List} as
	 * the form of return type.
	 * 
	 * @author Ziqing Luo
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param array
	 *            THe array needs being flattened
	 * @param civlsource
	 *            The CIVL source of the array
	 * @return a list of flatten elements of the given array.
	 */
	public List<SymbolicExpression> arrayFlattenList(State state,
			String process, SymbolicExpression array, CIVLSource civlsource);

	/**
	 * Given an array, a start index, and end index, returns the array which is
	 * the subsequence of the given array consisting of the elements in
	 * positions start index through end index minus one. The length of the new
	 * array is endIndex - startIndex. TODO move to libcivlc?
	 * 
	 * @param array
	 * @param startIndex
	 * @param endIndex
	 * @param assumption
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	SymbolicExpression getSubArray(SymbolicExpression array,
			NumericExpression startIndex, NumericExpression endIndex,
			State state, String process, CIVLSource source)
			throws UnsatisfiablePathConditionException;

	/**
	 * Computes the user-friendly string representation of a state.
	 * 
	 * @param state
	 *            The state whose string representation is to be computed.
	 * @return The user-friendly string representation of a state.
	 */
	StringBuffer stateToString(State state);

	/**
	 * <p>
	 * Computes the user-friendly string representation of a symbolic
	 * expression.
	 * </p>
	 * 
	 * <p>
	 * If the given expression is a pointer, then its string representation is
	 * computed according to the object that it refers to:
	 * <ul>
	 * <li>a variable: <code>& variable &lt;dyscope name></code>; <br>
	 * e.g.,
	 * 
	 * <pre>
	 * int a = 9; int * p = &a;
	 * </pre>
	 * 
	 * The representation of <code>p</code> would be <code>&a&lt;d0></code>
	 * assuming that the name of the dynamic scope of <code>a</code> is
	 * <code>d0</code>.</li>
	 * <li>an element of an array: <code>&array&lt;dyscope name>[index]</code>;<br>
	 * e.g.,
	 * 
	 * <pre>
	 * int a[5]; int *p = &a[1];
	 * </pre>
	 * 
	 * The representation of <code>p</code> would be <code>&a&lt;d0>[1]</code>
	 * assuming that the name of the dynamic scope of <code>a</code> is
	 * <code>d0</code>.</li>
	 * <li>a field of a struct: <code>&struct&lt;dyscope name>.field</code>;<br>
	 * e.g.,
	 * 
	 * <pre>
	 * typedef struct {int x; int y;} A; A s; int*p = &s.y;
	 * </pre>
	 * 
	 * The representation of p would be <code>&a&lt;d0>.y</code> assuming that
	 * the name of the dynamic scope of <code>a</code> is <code>d0</code>.</li>
	 * 
	 * <li>a heap cell:
	 * <code>heapObject&lt;dyscope name, malloc ID, number of malloc call></code>
	 * .</li>
	 * </ul>
	 * </p>
	 * 
	 * @param source
	 *            The source code information related to the symbolic expression
	 *            for error report if any.
	 * @param state
	 *            The state that the symbolic expression belongs to.
	 * @param symbolicExpression
	 *            The symbolic expression whose string representation is to be
	 *            computed.
	 * @return The user-friendly string representation of a state.
	 */
	String symbolicExpressionToString(CIVLSource source, State state,
			SymbolicExpression symbolicExpression);

	/**
	 * Computes the CIVL type of the object referring to by the given pointer.
	 * 
	 * @param soruce
	 *            The source code information related to the symbolic expression
	 *            for error report if any.
	 * @param state
	 *            The state that the given pointer belongs to.
	 * @param pointer
	 *            The pointer the type of whose object is to be computed.
	 * @return The CIVL type of the object referring to by the given pointer.
	 */
	CIVLType typeOfObjByPointer(CIVLSource soruce, State state,
			SymbolicExpression pointer);
}
