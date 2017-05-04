package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class MPIContractUtilities {

	static final String MPI_COMM_RANK_CONST = "$mpi_comm_rank";

	static final String MPI_COMM_SIZE_CONST = "$mpi_comm_size";

	static final String MPI_COMM_RANK_CALL = "MPI_Comm_rank";

	static final String MPI_COMM_SIZE_CALL = "MPI_Comm_size";

	static final String MPI_SNAPSHOT = "$mpi_snapshot";

	static final String COLLATE_COMPLETE = "$collate_complete";

	static final String COLLATE_ARRIVED = "$collate_arrived";

	static final String COLLATE_PRE_STATE = "_cs_pre";

	static final String COLLATE_POST_STATE = "_cs_post";

	static final String STATE_NULL = "$state_null";

	static final String ACSL_RESULT = "$result";

	static final String COLLATE_STATE_TYPE = "$collate_state";

	static TransformConfiguration getTransformConfiguration() {
		return new TransformConfiguration();
	}

	static ExpressionNode getStateNullExpression(Source source,
			NodeFactory nodeFactory) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, STATE_NULL));
	}

	static StatementNode withStatementWrapper(StatementNode body,
			ExpressionNode collateState, List<ExpressionNode> dependents,
			TransformConfiguration config, NodeFactory nodeFactory) {
		StatementNode withStmt = nodeFactory.newWithNode(body.getSource(),
				collateState.copy(), body.copy());
		if (config.getWith())
			return withStmt;

		if (config.getWithComplete() || config.getRunWithComplete()) {
			ExpressionNode functionIdentifier = nodeFactory
					.newIdentifierExpressionNode(body.getSource(),
							nodeFactory.newIdentifierNode(body.getSource(),
									COLLATE_COMPLETE));
			ExpressionNode collateComplete = nodeFactory.newFunctionCallNode(
					collateState.getSource(), functionIdentifier,
					Arrays.asList(collateState.copy()), null);
			StatementNode withCompleteStmt = nodeFactory.newWhenNode(
					collateComplete.getSource(), collateComplete, withStmt);

			if (config.getRunWithComplete())
				return nodeFactory.newRunNode(withCompleteStmt.getSource(),
						withCompleteStmt);
			else
				return withCompleteStmt;
		}
		if (config.getRunWithArrived()) {
			ExpressionNode functionIdentifier = nodeFactory
					.newIdentifierExpressionNode(body.getSource(),
							nodeFactory.newIdentifierNode(body.getSource(),
									COLLATE_ARRIVED));
			ExpressionNode allArrived = null;

			for (ExpressionNode dependent : dependents) {
				ExpressionNode arrived = nodeFactory.newFunctionCallNode(
						collateState.getSource(), functionIdentifier,
						Arrays.asList(collateState.copy(), dependent.copy()),
						null);
				Source arrivedSource = arrived.getSource();

				allArrived = allArrived == null
						? arrived
						: nodeFactory.newOperatorNode(arrivedSource,
								Operator.LAND,
								Arrays.asList(allArrived, arrived));

			}
			return nodeFactory.newRunNode(withStmt.getSource(), nodeFactory
					.newWhenNode(allArrived.getSource(), allArrived, withStmt));
		}
		return body;
	}

	static class TransformConfiguration {
		/**
		 * 8 bits filed, each bit from LEFT to RIGHT represents respectively:
		 * <code>With, WithComplete, RunWithComplete, RunWithArrived,
		 *  noResult, ignoreOld, havoc4Valid, inMPIBlock</code>
		 * 
		 * <p>
		 * noResult: No "\result" is allowed being in requirements
		 * </p>
		 * <p>
		 * ignoreOld: when transform requirements, 'old(expr)' expressions can
		 * be easily replaced with 'expr'
		 * </p>
		 * <p>
		 * havoc4Valid: Whether 'valid' expressions should be transformed to
		 * mallocs.
		 * </p>
		 * <p>
		 * inMPIBlock: report syntax error when using any MPI collective
		 * contract primitives in the sequential block.
		 * </p>
		 */
		private BitSet configs;

		private TransformConfiguration() {
			configs = new BitSet(8);
		}

		void setInMPIBlock(boolean value) {
			setValue(value, 7);
		}

		boolean isInMPIBlock() {
			return configs.get(7);
		}

		void setAlloc4Valid(boolean value) {
			setValue(value, 6);
		}

		boolean alloc4Valid() {
			return configs.get(6);
		}

		void setIgnoreOld(boolean value) {
			setValue(value, 5);
		}

		boolean ignoreOld() {
			return configs.get(5);
		}

		void setNoResult(boolean value) {
			setValue(value, 4);
		}

		boolean noResult() {
			return configs.get(4);
		}

		void setRunWithArrived(boolean value) {
			setValue(value, 3);
			if (value) {
				setValue(false, 0);
				setValue(false, 1);
				setValue(false, 2);
			}
		}

		boolean getRunWithArrived() {
			return configs.get(3);
		}

		void setRunWithComplete(boolean value) {
			setValue(value, 2);
			if (value) {
				setValue(false, 0);
				setValue(false, 1);
				setValue(false, 3);
			}
		}

		boolean getRunWithComplete() {
			return configs.get(2);
		}

		void setWithComplete(boolean value) {
			setValue(value, 1);
			if (value) {
				setValue(false, 0);
				setValue(false, 2);
				setValue(false, 3);
			}
		}

		boolean getWithComplete() {
			return configs.get(1);
		}

		void setWith(boolean value) {
			setValue(value, 0);
			if (value) {
				setValue(false, 1);
				setValue(false, 2);
				setValue(false, 3);
			}
		}

		boolean getWith() {
			return configs.get(0);
		}

		private void setValue(boolean value, int bit) {
			if (value)
				configs.set(bit);
			else
				configs.clear(bit);
		}
	}
}
