package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractsTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "contracts");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void with() {
		assertTrue(ui.run("verify", QUIET, filename("with.cvl")));
	}

	@Test
	public void with2() {
		assertTrue(ui.run("verify", QUIET, filename("with2.cvl")));
	}

	@Test
	public void with3() {
		assertTrue(ui.run("verify", QUIET, filename("with3.cvl")));
	}

	@Test
	public void update() {
		assertTrue(ui.run("verify", QUIET, filename("update.cvl")));
	}

	@Test
	public void update2() {
		assertTrue(ui.run("verify", QUIET, filename("update2.cvl")));
	}

	@Test
	public void guardSE() {
		assertTrue(ui.run("show -showProgram", QUIET,
				filename("contractsMPI/simpleGuard.cvl")));
	}

	@Test
	public void mpiAgree() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiAgree.c")));
	}

	@Test
	public void mpiRegion() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiRegion.c")));
	}

	@Test
	public void mpiOffset() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiOffset.c")));
	}

	@Test
	public void mpiValid() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiValid.c")));
	}

	@Test
	public void mpiValid2() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiValid2.c")));
	}

	@Test
	public void bcast() {
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -showProgram "
						+ "-mpiContract=broadcast",
				filename("contractsMPI/broadcast.c")));
	}

	@Test
	public void bcast_bad() {
		assertFalse(ui.run(
				"verify -input_mpi_nprocs=2 -showProgram "
						+ "-mpiContract=broadcast",
				filename("contractsMPI/broadcast_bad.c")));
	}

	@Test
	public void bcast_order() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=broadcast",
				filename("contractsMPI/broadcast_order.c")));
	}

	@Test
	public void gather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/gather.c")));
	}

	@Test
	public void gatherBad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/gather_bad.c")));
	}

	@Test
	public void allgather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=allgather",
				filename("contractsMPI/allgather.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/allgather.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=broadcast",
				filename("contractsMPI/allgather.c")));
	}

	@Test
	public void scatter() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=scatter",
				filename("contractsMPI/scatter.c")));
	}

	@Test
	public void scatter_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=scatter",
				filename("contractsMPI/scatter_bad.c")));
	}

	@Test
	public void reduce_sum() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=reduce_sum",
				filename("contractsMPI/reduce_sum.c")));
	}

	@Test
	public void wildcardError() {
		assertFalse(ui.run("verify -input_mpi_nprocs=3 -mpiContract=wildcard",
				filename("contractsMPI/wildcard-error.c")));
	}

	@Test
	public void wildcardGood() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=wildcard",
				filename("contractsMPI/wildcard-good.c")));
	}

	@Test
	public void diffusion1d_dev() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d_dev.c")));
	}

	@Test
	public void diffusion1d() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=update",
				filename("contractsMPI/diffusion1d.c")));
		assertTrue(
				ui.run("verify -input_mpi_nprocs=2 -mpiContract=exchange_ghost_cells",
						filename("contractsMPI/diffusion1d.c")));
	}

	@Test
	public void diffusion2d() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff2dIter",
				filename("contractsMPI/diffusion2d.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=update",
				filename("contractsMPI/diffusion2d.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=exchange",
				filename("contractsMPI/diffusion2d.c")));
	}

	@Test
	public void gj_elim() {
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -mpiContract=backwardReduce",
				filename("contractsMPI/gaussJordan_elimination_mpi.c")));
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -mpiContract=gaussianElimination",
				filename("contractsMPI/gaussJordan_elimination_mpi.c")));
	}

	@Test
	public void madre() {
		assertTrue(
				ui.run("verify -input_mpi_nprocs=2 -mpiContract=computeDirectMoves",
						filename("contractsMPI/madre_computeDirectMoves.c")));
	}

	@Test // extendQuant
	public void extendQuant() {
		assertTrue(
				ui.run("verify -showProgram=false -showTransitions=false -mpiContract=f ",
						QUIET, filename("extendQuant.c")));
	}
}
