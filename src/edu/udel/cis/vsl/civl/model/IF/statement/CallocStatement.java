package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * A statement for dynamic allocation of objects with clean and counted memory
 * space. Results from translation of an expression like: <br>
 * 
 * <code>int nElement = 10;</code><br>
 * <code>p = (double*)$calloc(nElements, sizeof(double));</code><br>
 * 
 * Where <code>nElements</code> is the number of elements. Executing such a
 * statement results in the creation of an array of elements of the specified
 * type (in this case, reals) and length (in this case, 10). The final size of
 * the allocated memory space is the multiplication of the size of element type
 * and the number of elements. <br>
 * <strong> Note that all bits in the allocated memory space will be cleaned as
 * 0. </strong>
 * 
 * @author Wenhao Wu (W.Wu)
 * 
 */
public interface CallocStatement extends Statement {

	/**
	 * The calloc statements in the model are indexed, so each has unique ID
	 * number. This returns it
	 * 
	 * @return the ID number of this calloc statement
	 */
	int getCallocId();

	/**
	 * The first argument to the $calloc function is an expression representing
	 * the number of element. This returns that expression. In the example, it
	 * is the expression <code>nElement</code>.
	 * 
	 * @return the first argument to $calloc
	 */
	Expression getScopeExpression();

	/**
	 * Returns the static type of the elements that are to be allocated. Each
	 * calloc statement must have a static type associated to it. The type can
	 * usually be determined by examining the cast expression which wraps the
	 * $calloc. In the example, the type is "double".
	 * 
	 * @return the type of elements to malloc.
	 */
	CIVLType getStaticElementType();

	/**
	 * This returns the dynamic (symbolic type) corresponding to the static
	 * element type. It is obtained by ignoring any array extent expressions.
	 * Hence if the static type is "array of float of length 3*n+1" the dynamic
	 * type will be "array of real". Since that dynamic type includes in its
	 * domain array of any length, it is an over-estimate of the types of
	 * elements that can be allocaged.
	 * 
	 * In the example, the dynamic type returned would be the symbolic type
	 * "real"
	 * 
	 * @return dynamic type corresonding to static element type
	 */
	SymbolicType getDynamicElementType();

	/**
	 * The object is the thing that is allocated; it is an array of a given
	 * number of elements of the specified type. This returns the dynamic type
	 * of the object (which is always an array type). In the example, it would
	 * be "array of real".
	 * 
	 * @return
	 */
	SymbolicArrayType getDynamicObjectType();

	/**
	 * 
	 * The second argument to the $calloc function is an integer expression
	 * specifying the size (number of bytes) to calloc. It is typically an
	 * exactly single type size such as "sizeof(t)".
	 * 
	 * In the example, it would be the expression <code>sizeof(double)</code>
	 * 
	 * @return the second argument to the $calloc statement, an integer-valued
	 *         expression, which is expected to be a single sizeof expression.
	 */
	Expression getSizeExpression();

	/**
	 * For every symbolic type, there is a symbolic constant of that type
	 * representing "undefined" value of that type. The name of that symbolic
	 * constant might very well be "UNDEFINED". This method returns the
	 * undefined value whose type is the dynamicObjectType. This is the
	 * expression used in place of an object that has been deallocated (by a
	 * <code>$free</code> instruction) until that object is swept up by the
	 * garbage collector.
	 * 
	 * In the example, this would return the symbolic constant UNDEFINED of type
	 * array of real.
	 * 
	 * @return undefined expression of dynamic object type
	 */
	SymbolicExpression getUndefinedObject();

	/**
	 * Returns the expression on the left-hand side of the assignment. In the
	 * example, this would be <code>p</code>. This expression will be assigned a
	 * pointer to the first element of the array object created by the calloc.
	 * 
	 * It may be null, but this is unusual.
	 * 
	 * @return the left hand side of the assignment
	 */
	LHSExpression getLHS();

	/**
	 * complete the type information of the calloc statement. This has to be
	 * done separatedly because it might involve the bundle type.
	 * 
	 * @param dynamicElementType
	 *            the dynamic element type
	 * @param dynamicObjectType
	 *            the dynamic object type
	 * @param undefinedObject
	 *            the initial undefined value for the object
	 */
	void complete(SymbolicType dynamicElementType,
			SymbolicArrayType dynamicObjectType,
			SymbolicExpression undefinedObject);
}
