package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * <p>
 * An MPICollectiveBlockClause is a block represents a group of contract clauses
 * that states a set of MPI properties. An MPI collective block is defined as <br>
 * <code>\mpi_collective(MPI_Comm, Collective_kind): {
 *   other contract clauses ... 
 * }</code>
 * </p>
 * <p>
 * An MPICollectiveBlockClause is signatured by a pair of MPI communicator and a
 * COLLECTIVE_KIND. It's obvious that for MPI programs, any communication
 * behaviors are associated to an MPI communicator. The COLLECTIVE_KIND denotes
 * the domain of the communication on the given MPI communicator. i.e.
 * <code> COLLECTIVE_KIND ::= P2P | COL | BOTH </code>
 * </p>
 * <p>
 * MPICollectiveBlockClause cannot be nested.
 * </p>
 * <p>
 * Please be aware of this: it is IMPORTANT to claim that the word "collective"
 * here is somewhat different from the collective routines defined in MPI
 * standard. An MPI collective contracts defines the behavior of a function
 * should satisfy some collective properties no matter if collective routines is
 * used inside the function. e.g. If a function requires all processes in
 * MPI_COMM_WORLD execute itself collectively and inside the function it's just
 * an MPI_Sendrecv routine, this function has a collective behavior.
 * </p>
 * 
 * @author ziqing
 *
 */
public interface MPICollectiveBlockClause extends ContractClause {
	/**
	 * This enumerator represents three different domains of clauses in the
	 * collective block. <li>
	 * <ol>
	 * P2P stands for all point-2-point communications in the given
	 * communicator.
	 * </ol>
	 * <ol>
	 * COL stands for all collective communications in the given communicator
	 * </ol>
	 * <ol>
	 * BOTH stands for all point-2-point and collective communications in the
	 * given communicator.
	 * </ol>
	 * </li>
	 * 
	 * @author ziqing
	 *
	 */
	public enum COLLECTIVE_KIND {
		P2P, COL, BOTH
	}

	/**
	 * Returns the {@link Expression} of the given MPI communicator
	 * 
	 * @return
	 */
	Expression getMPIComm();

	/**
	 * Returns the {@link COLLECTIVE_KIND} of the MPI collective block in where
	 * this clause is.
	 * 
	 * @return
	 */
	COLLECTIVE_KIND getCollectiveKind();

	/**
	 * Returns the {@link ClauseSequence} of contract clauses belonging to this
	 * block
	 * 
	 * @return
	 */
	ClauseSequence getBody();
}
