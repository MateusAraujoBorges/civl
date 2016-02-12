package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An common interface for difference contract clauses. Different contract
 * clauses are denoted by {@link ContractClauseKind}.
 * 
 * @author ziqing
 *
 */
public interface ContractClause extends Expression {
	public enum ContractClauseKind {
		/**
		 * defines memory units assigned by the function
		 */
		ASSIGNS_READS,
		/**
		 * an "assumes" clause
		 */
		ASSUMES,
		/**
		 * An "behavior" node encodes a named behavior block
		 */
		BEHAVIOR,
		/**
		 * An "completeness" node encodes either a complete or disjoint clause
		 */
		COMPLETENESS,
		/**
		 * defines features of the dependent processes of the current one
		 */
		DEPENDS,
		/**
		 * An "ensures" node encodes a post-condition in a procedure contract. A
		 * node of this kind can be safely cast to {@link EnsuresNode}.
		 */
		ENSURES,
		/**
		 * A "guard" node represents the guard of a CIVL-C function. A node of
		 * this kind may be safely cast to {@link GuardNode}.
		 */
		GUARDS,
		/**
		 * A "requires" node represents a pre-condition in a CIVL-C procedure
		 * contract. May be safely cast to {@link RequiresNode}.
		 */
		REQUIRES,
		/**
		 * A sequence of contract clauses
		 */
		SEQUENCE,
		/**
		 * A "\mpi_collective" node introduces a block of contracts which should
		 * satisfy mpi collective behaviors.
		 */
		MPI_COLLECTIVE
	};

	/**
	 * Returns a {@link ContractClauseKind} represents the clause kind of the a
	 * contract clause.
	 * 
	 * @return
	 */
	ContractClauseKind contractKind();

	@Override
	ContractClause replaceWith(ConditionalExpression oldExpr, Expression newExpr);
}
