package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICollectiveKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.WaitsforNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * This class represents a contract block, i.e. either all of the contracts for
 * sequential properties or one MPI collective contract block. A contract block
 * contains a set of {@link ConditionalClauses} which represents the body of the
 * contract block.
 * 
 * @author ziqing
 *
 */
class FunctionContractBlock {
	/**
	 * The expression represents an MPI communicator which associates to an MPI
	 * collective block.
	 */
	private ExpressionNode mpiComm;

	/**
	 * The expression represents the choice of which MPI communicator is used
	 * for the contracts in the contract block: point-2-point or collective.
	 */
	private MPICollectiveKind collectiveKind;

	/**
	 * A list of {@link ConditionalClauses} which represents the body of the
	 * collective blocks.
	 */
	private List<ConditionalClauses> behaviors;

	/**
	 * The big {@link Source} associates to the contract block
	 */
	private Source source;

	/**
	 * A flag indicates if the contract block is completed. A complete contract
	 * block should never contain any {@link ConditionalClauses} that saves
	 * empty clauses.
	 */
	private boolean complete = false;

	private FunctionContractBlock(ExpressionNode mpiComm,
			MPICollectiveKind kind, Source source) {
		behaviors = new LinkedList<>();
		this.mpiComm = mpiComm;
		this.collectiveKind = kind;
		this.source = source;
	}

	/* *************************** static methods ***************************/
	/**
	 * Parse a chunk of contracts into several {@link FunctionContractBlock}s.
	 * Each of which represents either the whole chunk of sequential contracts
	 * or a collective block.
	 * 
	 * @param contractNodes
	 *            A sequence of {@link ContractNode}s
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 * @return A list of {@link FunctionContractBlock}s which represent the
	 *         given contractNodes. If there exists any sequential contract, it
	 *         will be in the first element of the returned list.
	 */
	static List<FunctionContractBlock> parseContract(
			SequenceNode<ContractNode> contractNodes, NodeFactory nodeFactory) {
		List<FunctionContractBlock> results = new LinkedList<>();
		FunctionContractBlock seqBlock = new FunctionContractBlock(null, null,
				contractNodes.getSource());

		// parse default behavior:
		parseClausesInBehavior(seqBlock, contractNodes, nodeFactory);
		// parse sequential behaviors:
		for (ContractNode contract : contractNodes)
			if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(seqBlock,
						((BehaviorNode) contract).getBody(), nodeFactory);
		if (seqBlock.complete())
			results.add(seqBlock);
		// parse MPI collective blocks
		for (ContractNode contract : contractNodes)
			if (contract.contractKind() == ContractKind.MPI_COLLECTIVE) {
				FunctionContractBlock block = parseMPICollectiveBlock(
						(MPICollectiveBlockNode) contract, nodeFactory);

				if (block.complete())
					results.add(block);
			}
		return results;
	}

	/**
	 * Parse a {@link MPICollectiveBlockNode} into a
	 * {@link FunctionContractBlock}.
	 * 
	 * @param mpiBlockNode
	 *            A node represents a MPI collective contract block
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 * @return An instance of {@link FunctionContractBlock}.
	 */
	static private FunctionContractBlock parseMPICollectiveBlock(
			MPICollectiveBlockNode mpiBlockNode, NodeFactory nodeFactory) {
		ExpressionNode mpiComm = mpiBlockNode.getMPIComm();
		FunctionContractBlock block = new FunctionContractBlock(mpiComm,
				mpiBlockNode.getCollectiveKind(), mpiBlockNode.getSource());

		parseClausesInBehavior(block, mpiBlockNode.getBody(), nodeFactory);
		for (ContractNode contract : mpiBlockNode.getBody())
			if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(block,
						((BehaviorNode) contract).getBody(), nodeFactory);
		return block;
	}

	/**
	 * Parse a behavior block into an instance of {@link ConditionalClauses} and
	 * adds it to associated {@link FunctionContractBlock}.
	 * 
	 * @param currentBlock
	 *            The contract block where the behavior block is in.
	 * @param contracts
	 *            A sequence of contracts representing a behavior block
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 */
	static private void parseClausesInBehavior(
			FunctionContractBlock currentBlock,
			SequenceNode<ContractNode> contracts, NodeFactory nodeFactory) {
		ExpressionNode assumptions = null;

		// Collects assumptions:
		for (ContractNode contract : contracts)
			if (contract.contractKind() == ContractKind.ASSUMES) {
				ExpressionNode assumes = ((AssumesNode) contract)
						.getPredicate();

				assumptions = assumptions == null
						? assumes
						: nodeFactory.newOperatorNode(assumes.getSource(),
								Operator.LAND, assumptions, assumes);
			}

		ConditionalClauses condClauses = currentBlock.new ConditionalClauses(
				assumptions);

		// Collects clauses which specifies predicates:
		for (ContractNode contract : contracts) {
			ContractKind kind = contract.contractKind();

			switch (kind) {
				case REQUIRES :
					condClauses.addRequires(
							((RequiresNode) contract).getExpression());
					break;
				case ENSURES :
					condClauses.addEnsures(
							((EnsuresNode) contract).getExpression());
					break;
				case WAITSFOR :
					condClauses.addWaitsfor(
							((WaitsforNode) contract).getArguments());
					break;
				case ASSIGNS_READS : {
					AssignsOrReadsNode assigns = (AssignsOrReadsNode) contract;
					SequenceNode<ExpressionNode> memList;

					if (!assigns.isAssigns())
						break;
					memList = assigns.getMemoryList();
					if (memList.numChildren() <= 0
							|| memList.getSequenceChild(0)
									.expressionKind() != ExpressionKind.NOTHING)
						condClauses.addAssigns(assigns.getMemoryList());
					break;
				}
				default :
					// do nothing.
			}
		}
		currentBlock.addConditionalClauses(condClauses);
	}

	/* *********************** package private getters ***********************/
	boolean isSequentialBlock() {
		return collectiveKind == null;
	}

	ExpressionNode getMPIComm() {
		return mpiComm;
	}

	MPICollectiveKind getKind() {
		return collectiveKind;
	}

	Source getContractBlockSource() {
		return source;
	}

	Iterable<ConditionalClauses> getBehaviorsInBlock() {
		return behaviors;
	}

	/**
	 * This class represents a contract behavior. Without loss of generality,
	 * there is always a default behavior which has no assumption and no name.
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
		ExpressionNode getRequires(NodeFactory nodeFactory) {
			if (requiresSet.isEmpty())
				return null;

			ExpressionNode result = requiresSet.remove(0);

			result.remove();
			for (ExpressionNode requires : requiresSet) {
				requires.remove();
				result = nodeFactory.newOperatorNode(requires.getSource(),
						Operator.LAND, result, requires);
			}
			requiresSet.clear();
			requiresSet.add(result);
			return requiresSet.get(0);
		}

		/**
		 * Returns all ensures expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		ExpressionNode getEnsures(NodeFactory nodeFactory) {
			if (ensuresSet.isEmpty())
				return null;

			ExpressionNode result = ensuresSet.remove(0);

			result.remove();
			for (ExpressionNode ensures : ensuresSet) {
				ensures.remove();
				result = nodeFactory.newOperatorNode(ensures.getSource(),
						Operator.LAND, result, ensures);
			}
			ensuresSet.clear();
			ensuresSet.add(result);
			return ensuresSet.get(0);

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
