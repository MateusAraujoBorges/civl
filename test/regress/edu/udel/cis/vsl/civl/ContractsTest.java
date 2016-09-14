package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import jdk.nashorn.internal.ir.annotations.Ignore;

public class ContractsTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "contracts");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Ignore
	public void with() {
		assertTrue(ui.run("verify", QUIET, filename("with.cvl")));
	}

	@Ignore
	public void with2() {
		assertTrue(ui.run("verify", QUIET, filename("with2.cvl")));
	}

	@Ignore
	public void with3() {
		assertTrue(ui.run("verify", QUIET, filename("with3.cvl")));
	}

	@Ignore
	public void update() {
		assertTrue(ui.run("verify", QUIET, filename("update.cvl")));
	}

	@Ignore
	public void update2() {
		assertTrue(ui.run("verify", QUIET, filename("update2.cvl")));
	}

	@Ignore
	public void guardSE() {
		assertTrue(ui.run("show -showProgram", QUIET,
				filename("contractsMPI/simpleGuard.cvl")));
	}

	@Ignore
	public void mpiAgree() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiAgree.c")));
	}

	@Ignore
	public void mpiRegion() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiRegion.c")));
	}

	@Ignore
	public void mpiOffset() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiOffset.c")));
	}

	@Ignore
	public void mpiValid() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiValid.c")));
	}

	@Ignore
	public void mpiValid2() {
		assertTrue(ui.run("verify -input_mpi_nprocs=5 -mpiContract=target",
				QUIET, filename("contractsMPI/simpleMpiValid2.c")));
	}

	@Ignore
	public void bcast() {
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -showProgram "
						+ "-mpiContract=broadcast",
				filename("contractsMPI/broadcast.c")));
	}

	@Ignore
	public void bcast_bad() {
		assertFalse(ui.run(
				"verify -input_mpi_nprocs=2 -showProgram "
						+ "-mpiContract=broadcast",
				filename("contractsMPI/broadcast_bad.c")));
	}

	@Ignore
	public void bcast_order() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=broadcast",
				filename("contractsMPI/broadcast_order.c")));
	}

	@Ignore
	public void gather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/gather.c")));
	}

	@Ignore
	public void gatherBad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/gather_bad.c")));
	}

	@Ignore
	public void allgather() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=allgather",
				filename("contractsMPI/allgather.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=gather",
				filename("contractsMPI/allgather.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=broadcast",
				filename("contractsMPI/allgather.c")));
	}

	@Ignore
	public void scatter() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=scatter",
				filename("contractsMPI/scatter.c")));
	}

	@Ignore
	public void scatter_bad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=scatter",
				filename("contractsMPI/scatter_bad.c")));
	}

	@Ignore
	public void reduce_sum() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=reduce_sum",
				filename("contractsMPI/reduce_sum.c")));
	}

	@Ignore
	public void wildcardError() {
		assertFalse(ui.run("verify -input_mpi_nprocs=3 -mpiContract=wildcard",
				filename("contractsMPI/wildcard-error.c")));
	}

	@Ignore
	public void wildcardGood() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=wildcard",
				filename("contractsMPI/wildcard-good.c")));
	}

	@Ignore
	public void diffusion1dIterDev() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d_dev.c")));
	}

	@Ignore
	public void diffusion1dDevUpdateBad() {
		// update is bad when it is called by "diff1dIter"
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d_dev-bad-update.c")));
	}

	@Ignore
	public void diffusion1dIter() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d.c")));
	}

	@Ignore
	public void diffusion1dIterBad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff1dIter",
				filename("contractsMPI/diffusion1d-bad-diffIter.c")));
	}

	@Ignore
	public void diffusion1dUpdate() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=update",
				filename("contractsMPI/diffusion1d.c")));
	}

	@Ignore
	public void diffusion1dExchange() {
		assertTrue(
				ui.run("verify -input_mpi_nprocs=2 -mpiContract=exchange_ghost_cells",
						filename("contractsMPI/diffusion1d.c")));
	}

	@Ignore
	public void diffusion2d() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=exchange",
				filename("contractsMPI/diffusion2d.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=update",
				filename("contractsMPI/diffusion2d.c")));
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=diff2dIter",
				filename("contractsMPI/diffusion2d.c")));
	}

	@Ignore
	public void diffusion2d_dev2() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=exchange",
				filename("contractsMPI/diffusion2d_dev2.c")));
	}

	@Ignore
	public void quantifiedRemote() {
		assertTrue(ui.run("show -mpiContract=foo",
				filename("contractsMPI/quantifiedRemote.c")));
	}

	@Ignore
	public void gj_elim() {
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -mpiContract=backwardReduce",
				filename("contractsMPI/gaussJordan_elimination_mpi.c")));
		assertTrue(ui.run(
				"verify -input_mpi_nprocs=2 -mpiContract=gaussianElimination",
				filename("contractsMPI/gaussJordan_elimination_mpi.c")));
	}

	@Ignore
	public void madre() {
		assertTrue(
				ui.run("verify -input_mpi_nprocs=2 -mpiContract=computeDirectMoves",
						filename("contractsMPI/madre_computeDirectMoves.c")));
	}

	@Ignore // extendQuant
	public void extendQuant() {
		assertTrue(
				ui.run("verify -showProgram=false -showTransitions=false -mpiContract=f ",
						QUIET, filename("extendQuant.c")));
	}
}
