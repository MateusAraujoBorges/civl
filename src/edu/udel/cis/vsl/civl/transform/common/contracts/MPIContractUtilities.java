package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.BitSet;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class MPIContractUtilities {

	/* **************** Intermediate variable names: *****************/

	static final String CIVL_CONTRACT_PREFIX = "_cc";

	static final String COLLATE_STATE_PREFIX = CIVL_CONTRACT_PREFIX + "_cs";

	static final String PRE_COLLATE_STATE = COLLATE_STATE_PREFIX + "_pre";

	static final String POST_COLLATE_STATE = COLLATE_STATE_PREFIX + "_post";

	static final String ASSIGN_VAR_PREFIX = CIVL_CONTRACT_PREFIX + "_assign_";

	static final String HEAP_VAR_PREFIX = CIVL_CONTRACT_PREFIX + "_heap_";

	static final String EXTENT_VAR_PREFIX = CIVL_CONTRACT_PREFIX + "_extent_";

	/* **************** Artificial identifier names: *****************/

	static final String MPI_COMM_RANK_CONST = "$mpi_comm_rank";

	static final String MPI_COMM_SIZE_CONST = "$mpi_comm_size";

	static final String MPI_COMM_RANK_CALL = "MPI_Comm_rank";

	static final String MPI_COMM_SIZE_CALL = "MPI_Comm_size";

	static final String MPI_BARRIER_CALL = "MPI_Barrier";

	static final String MPI_SNAPSHOT = "$mpi_snapshot";

	static final String MPI_UNSNAPSHOT = "$mpi_unsnapshot";

	static final String MPI_ASSIGNS = "$mpi_assigns";

	static final String MPI_EXTENT_OF = "$mpi_extentof";

	static final String MPI_CHECK_EMPTY_COMM = "$mpi_comm_empty";

	final static String MPI_COMM_WORLD = "MPI_COMM_WORLD";

	static final String MPI_COMM_P2P_MODE = "P2P";

	static final String MPI_COMM_COL_MODE = "COL";

	static final String COLLATE_COMPLETE = "$collate_complete";

	static final String COLLATE_ARRIVED = "$collate_arrived";

	static final String COLLATE_PRE_STATE = "_cs_pre";

	static final String COLLATE_POST_STATE = "_cs_post";

	static final String STATE_NULL = "$state_null";

	static final String COLLATE_STATE_TYPE = "$collate_state";

	static final String COLLATE_GET_STATE_CALL = "$collate_get_state";

	static final String ACSL_RESULT_VAR = "$result";

	static final String HAVOC = "$havoc";

	static TransformConfiguration getTransformConfiguration() {
		return new TransformConfiguration();
	}

	static ExpressionNode getStateNullExpression(Source source,
			NodeFactory nodeFactory) {
		return nodeFactory.newStatenullNode(source);
	}

	static String nextAssignName(int counter) {
		return ASSIGN_VAR_PREFIX + counter;
	}

	static String nextAllocationName(int count) {
		return HEAP_VAR_PREFIX + count;
	}

	static String nextExtentName(int count) {
		return EXTENT_VAR_PREFIX + count;
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
