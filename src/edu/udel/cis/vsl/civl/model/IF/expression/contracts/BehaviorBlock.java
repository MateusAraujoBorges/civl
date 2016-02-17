package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.util.IF.Pair;

/**
 * This class represents a named behavior block which is defined in ACSL(v1.4
 * 2.3.3)
 * 
 * @author ziqing
 *
 */
public interface BehaviorBlock extends ContractClause {
	/**
	 * Returns the name of the behavior block.
	 * 
	 * @return
	 */
	String behaviorName();

	/**
	 * A behavior block consists of a set of contract clauses that are only
	 * significant under a specific assumption. Thus the structure of one block
	 * is a expression representing the assumption and a sequence of contract
	 * clauses.
	 * 
	 * @return
	 */
	Pair<Expression, ClauseSequence> getSubBlock();
}