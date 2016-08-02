package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;

/**
 * This class represents a set of MPI contract expressions:
 * <ol>
 * <li>\mpi_empty_in: expresses that a receiving buffer is empty.</li>
 * <li>\mpi_empty_out: expresses that a sending buffer is empty.</li>
 * <li>\mpi_agree: expresses that an variable is same at the beginning for all
 * processes.</li>
 * <li>\mpi_equals: expresses that two pointers are pointing to the equal
 * obejects.</li>
 * <li>\mpi_region: represents an memory object in an MPI program.</li>
 * </ol>
 * 
 * @author ziqingluo
 *
 */
public interface MPIContractExpression extends Expression {
	static public enum MPI_CONTRACT_EXPRESSION_KIND {
		/**
		 * The expression in CIVL model representing the \mpi_agree expression
		 * in ACSL annotations:
		 */
		MPI_AGREE,
		/**
		 * The expression in CIVL model representing the \mpi_equals expression
		 * in ACSL annotations:
		 */
		MPI_EQUALS,
		/**
		 * The expression in CIVL model representing the \mpi_extent expression
		 * in ACSL annotations:
		 */
		MPI_EXTENT,
		/**
		 * The expression in CIVL model representing the \mpi_offset expression
		 * in ACSL annotations:
		 */
		MPI_OFFSET,
		/**
		 * The expression in CIVL model representing the \mpi_region expression
		 * in ACSL annotations:
		 */
		MPI_REGION,
		/**
		 * The expression in CIVL model representing the \mpi_valid expression
		 * in ACSL annotations:
		 */
		MPI_VALID
	}

	/**
	 * Returns MPI_CONTRACT_EXPRESSION_KIND which denotes the exact kind of a
	 * general MPI contract expression.
	 * 
	 * @return
	 */
	MPI_CONTRACT_EXPRESSION_KIND mpiContractKind();

	/**
	 * The communicator associates with the MPI contract expression. The MPI
	 * communicator should be defined at the MPI collective behavior block.
	 * 
	 * @return
	 */
	Expression communicator();

	/**
	 * Returns an array of arguments of an MPI contract expression.
	 * 
	 * @return
	 */
	Expression[] arguments();

	/**
	 * <p>
	 * <b>Summary</b> Returns the MPI communication pattern. Currently it's
	 * either P2P (point-2-point) or COL (collective)
	 * </p>
	 * 
	 * @return
	 */
	MPICommunicationPattern getMpiCommunicationPattern();
}
