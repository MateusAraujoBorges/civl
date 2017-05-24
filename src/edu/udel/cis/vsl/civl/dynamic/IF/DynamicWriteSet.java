package edu.udel.cis.vsl.civl.dynamic.IF;

import edu.udel.cis.vsl.civl.dynamic.immutable.ImmutableDynamicWriteSet;
import edu.udel.cis.vsl.civl.library.civlc.LibcivlcExecutor;
import edu.udel.cis.vsl.civl.library.mpi.LibmpiExecutor;
import edu.udel.cis.vsl.civl.library.time.LibtimeExecutor;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.common.CommonExecutor;
import edu.udel.cis.vsl.civl.state.common.immutable.ImmutableStateFactory;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * <p>
 * This class represents a write set value which is formed dynamically. A
 * dynamic write set stores a set of memory location references which refer to
 * the memory locations that are changed ( from a point that starts monitoring
 * "write" operations).
 * </p>
 * 
 * <p>
 * An instance of this class is a referenced value for a {@link Variable} with
 * $mem type.
 * </p>
 * 
 * <p>
 * <b>Here is just a record of Java methods, calling of which will change the
 * write set</b>
 * <ul>
 * <li>The private methods in {@link CommonExecutor}, there are two of them:
 * assignCore and assignLHS</li>
 * <li>
 * {@link ImmutableStateFactory#deallocate(edu.udel.cis.vsl.civl.state.IF.State, SymbolicExpression, int, int, int)}
 * </li>
 * <li>executeMalloc and malloc in {@link CommonExecutor}</li> <br>
 * TODO: can all the following go through the executor's assign() ?
 * <li>{@link LibmpiExecutor#executeNewGcomm} (TODO: is this needed to be
 * recorded ?)</li>
 * <li>{@link LibtimeExecutor#executeLocalTime}</li>
 * <li>{@link CommonExecutor#executeNextInDomain} (TODO: this one needs some
 * special non-concretet handling)</li>
 * <li>{@link LibcivlcExecutor#executeNextTimeCount}</li>
 * </ul>
 * </p>
 * 
 * @author ziqing (Ziqing Luo)
 */
public interface DynamicWriteSet extends Iterable<SymbolicExpression> {

	/**
	 * <p>
	 * Add a set of memory location references to the write set
	 * </p>
	 * 
	 * @param pointer
	 *            A set of {@link SymbolicExpression} which represents a set of
	 *            concrete pointer.
	 * @return An instance which has one more element tha this iff the pointer
	 *         is not in this write set.
	 */
	public DynamicWriteSet addReference(SymbolicExpression pointer);

	/**
	 * <p>
	 * Apply an {@link UnaryOperator} on the set of memory location references.
	 * If the operator changes nothing, return this instance.
	 * </p>
	 * 
	 * @param operator
	 * @return An instance whose references are obtained by applying the
	 *         operator on ones of this
	 */
	public DynamicWriteSet apply(UnaryOperator<SymbolicExpression> operator);

	/**
	 * <p>
	 * Simplify the reference set using the given {@link Reasoner}.
	 * </p>
	 * 
	 * @param reasoner
	 *            An instance of a {@link Reasoner}.
	 * @return An {@link ImmutableDynamicWriteSet} instance whose symbolic
	 *         contents are simplified.
	 */
	public DynamicWriteSet simplify(Reasoner reasoner);
}
