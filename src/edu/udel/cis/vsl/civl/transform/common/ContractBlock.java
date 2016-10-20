package edu.udel.cis.vsl.civl.transform.common;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICollectiveKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.util.IF.Pair;

/**
 * This class represents a contract block, i.e. either all of the contracts for
 * sequential properties or one MPI collective contract block. A contract block
 * contains a set of {@link ConditionalClauses} which represents the body of the
 * contract block.
 * 
 * @author ziqing
 *
 */
class ContractBlock {
	/**
	 * The expression represents an MPI communicator which associates to an MPI
	 * collective block.
	 */
	private ExpressionNode mpiComm;
	/**
	 * The expression represents the choice of which MPI communicator is used
	 * for the contracts in the contract block: point-2-point or collective.
	 */
	private MPICollectiveKind pattern;
	/**
	 * A list of {@link ConditionalClauses} which represents the body of the
	 * block.
	 */
	private List<ConditionalClauses> behaviors;

	/**
	 * The {@link Source} associates to the contract block
	 */
	private Source source;

	/**
	 * A flag indicates if the contract block is completed. A complete contract
	 * block should never contain any {@link ConditionalClauses} that saves
	 * empty clauses.
	 */
	private boolean complete = false;

	ContractBlock(ExpressionNode mpiComm, MPICollectiveKind pattern,
			Source source) {
		behaviors = new LinkedList<>();
		this.mpiComm = mpiComm;
		this.pattern = pattern;
		this.source = source;
	}
	/* *************************** Simple getters ***************************/
	ConditionalClauses newConditionClauses(ExpressionNode condition) {
		return new ConditionalClauses(condition);
	}

	/* *************************** Simple getters ***************************/
	ExpressionNode getMPIComm() {
		return mpiComm;
	}

	MPICollectiveKind getPattern() {
		return pattern;
	}

	Source getContractBlockSource() {
		return source;
	}

	Iterable<ConditionalClauses> getBehaviorsInBlock() {
		return behaviors;
	}

	/**
	 * This class represents a contract behavior. Without loss of generality,
	 * there is always a default behavior which has no assumption and name.
	 * 
	 * A contract behavior consists of a set of contract clauses which specify
	 * properties. Currently it consists of "requires", "ensures" and "waitsfor"
	 * clauses. The design of this class is make it extensible if new clauses
	 * will be supported later.
	 * 
	 * @author ziqing
	 *
	 */
	class ConditionalClauses {
		/**
		 * The condition which comes from the assumption of a behavior:
		 */
		final ExpressionNode condition;

		private List<ExpressionNode> requiresSet;

		private List<ExpressionNode> ensuresSet;

		private List<ExpressionNode> waitsforSet;

		private List<ExpressionNode> assignsSet;

		private ConditionalClauses(ExpressionNode condition) {
			this.condition = condition;
			requiresSet = new LinkedList<>();
			ensuresSet = new LinkedList<>();
			waitsforSet = new LinkedList<>();
			assignsSet = new LinkedList<>();
		}

		/**
		 * Add an expression of a "requires" clause.
		 * 
		 * @param requires
		 */
		void addRequires(ExpressionNode requires) {
			requiresSet.add(requires);
		}

		/**
		 * Add an expression of a "ensures" clause.
		 * 
		 * @param requires
		 */
		void addEnsures(ExpressionNode ensures) {
			ensuresSet.add(ensures);
		}

		/**
		 * Add a set of arguments of a "waitsfor" clause.
		 * 
		 * @param requires
		 */
		void addWaitsfor(SequenceNode<ExpressionNode> waitsforArgs) {
			for (ExpressionNode arg : waitsforArgs)
				waitsforSet.add(arg);
		}

		/**
		 * Add a set of arguments of a "assigns" clause.
		 * 
		 * @param assignsArgs
		 */
		void addAssigns(SequenceNode<ExpressionNode> assignsArgs) {
			for (ExpressionNode arg : assignsArgs)
				assignsSet.add(arg);
		}

		/**
		 * Returns all requires expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		List<ExpressionNode> getRequires(NodeFactory nodeFactory) {
			if (requiresSet.isEmpty())
				return requiresSet;

			ExpressionNode result = requiresSet.remove(0);

			result.remove();
			for (ExpressionNode requires : requiresSet) {
				requires.remove();
				result = nodeFactory.newOperatorNode(requires.getSource(),
						Operator.LAND, result, requires);
			}
			requiresSet.clear();
			requiresSet.add(result);
			return requiresSet;
		}

		/**
		 * Returns all ensures expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		List<ExpressionNode> getEnsures(NodeFactory nodeFactory) {
			if (ensuresSet.isEmpty())
				return ensuresSet;

			ExpressionNode result = ensuresSet.remove(0);

			result.remove();
			for (ExpressionNode ensures : ensuresSet) {
				ensures.remove();
				result = nodeFactory.newOperatorNode(ensures.getSource(),
						Operator.LAND, result, ensures);
			}
			ensuresSet.clear();
			ensuresSet.add(result);
			return ensuresSet;

		}

		/**
		 * Returns a list of arguments of "waitsfor" clauses
		 * 
		 * @param nodeFactory
		 * @return
		 */
		List<ExpressionNode> getWaitsfors() {
			return waitsforSet;
		}

		/**
		 * Return a list of assigns arguments.
		 * 
		 * @return
		 */
		List<ExpressionNode> getAssignsArgs() {
			return assignsSet;
		}
	}

	/**
	 * Clean up all {@link ConditionalClauses} in this contract block. If a
	 * {@link ConditionalClauses} has empty clauses, remove it.
	 * 
	 * @return True if and only if there is at least one
	 *         {@link ConditionalClauses} remaining at the end of the function.
	 */
	boolean complete() {
		List<ConditionalClauses> newBehaviors = new LinkedList<>();

		for (ConditionalClauses behav : behaviors) {
			if (!(behav.requiresSet.isEmpty() && behav.ensuresSet.isEmpty()
					&& behav.waitsforSet.isEmpty()))
				newBehaviors.add(behav);
		}
		complete = true;
		behaviors = newBehaviors;
		return !behaviors.isEmpty();
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The contract block must be complete
	 * </p>
	 * 
	 * @return A list of {@link ConditionalClauses} which is the body of the
	 *         contract block.
	 */
	List<ConditionalClauses> getConditionalClauses() {
		assert complete : "Cannot get ConditionalClauses before the contract block is complete";
		return behaviors;
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The contract block must be complete
	 * </p>
	 * 
	 * @return A list of pairs. Each pair consists of a conditional expression
	 *         and a list of arguments of "waitsfor" clauses.
	 */
	List<Pair<ExpressionNode, List<ExpressionNode>>> getConditionalWaitsfors() {
		assert complete : "Cannot get ConditionalClauses before the contract block is complete";
		List<Pair<ExpressionNode, List<ExpressionNode>>> results = new LinkedList<>();

		for (ConditionalClauses condClause : behaviors)
			results.add(
					new Pair<>(condClause.condition, condClause.waitsforSet));
		return results;
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The contract block must NOT be complete
	 * </p>
	 * <p>
	 * <b>Summary:</b> Add a {@link ConditionalClauses} into the contract block.
	 * </p>
	 */
	void addConditionalClauses(ConditionalClauses clauses) {
		assert !complete : "Cannot add ConditionalClauses after the contract block is complete";
		behaviors.add(clauses);
	}
}
