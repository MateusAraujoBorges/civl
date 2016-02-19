package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractTest {
	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "contracts");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Ignore
	public void collective_assert() {
		assertFalse(ui.run(
				TestConstants.VERIFY, TestConstants.NO_PRINTF, TestConstants.QUIET,
				"-input_mpi_nprocs=3", TestConstants.MPI_CONTRACT,
				filename("wildcard_coassert_bad.c")));
		
		assertTrue(ui
				.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
						"-input_mpi_nprocs=4", TestConstants.POTENTIAL_DEADLOCK,
						TestConstants.MPI_CONTRACT, TestConstants.QUIET,
						filename("wildcard_coassert_barrier.c")));
		
		assertTrue(ui
				.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
						"-input_mpi_nprocs=5", TestConstants.POTENTIAL_DEADLOCK,
						TestConstants.MPI_CONTRACT, TestConstants.QUIET,
						filename("reduce_coassert.c")));
		
		assertFalse(ui
				.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
						"-input_mpi_nprocs=4", TestConstants.POTENTIAL_DEADLOCK,
						TestConstants.errorBound(10), TestConstants.MPI_CONTRACT,
						TestConstants.QUIET, filename("wildcard_coassert_bad.c")));
	}

	@Ignore
	// coverage test: only for covering parts of code, the example may not
	// understandable for human beings.
	public void collective_assert_coverage() {
		assertFalse(ui
				.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
						TestConstants.NO_PRINTF, TestConstants.errorBound(10),
						"-input_mpi_nprocs=3", TestConstants.MPI_CONTRACT,
						TestConstants.QUIET, filename("coassert_cover.c")));
	}

	@Ignore
	public void result() {
		assertTrue(ui
				.run(TestConstants.SHOW, TestConstants.SHOW_MODEL,
						TestConstants.MPI_CONTRACT, filename("result.c")));
	}

	@Ignore
	public void isRecvBufEmptyOK() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.MIN,
				TestConstants.MPI_CONTRACT, "-input_mpi_nprocs=4",
				TestConstants.QUIET, filename("isRecvBufEmpty_OK.c")));
	}

	@Ignore
	public void isEmptyRecvBufBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.MPI_CONTRACT,
				TestConstants.QUIET, filename("isRecvBufEmpty_BAD.c")));
	}

	@Ignore
	public void wildcard_contract_bad() {
		assertFalse(ui
				.run(TestConstants.VERIFY, TestConstants.MIN,
						TestConstants.POTENTIAL_DEADLOCK, TestConstants.MPI_CONTRACT,
						"-input_mpi_nprocs=3", TestConstants.QUIET,
						filename("wildcard_contract_bad.c")));
		ui.run(TestConstants.REPLAY, TestConstants.QUIET, filename("wildcard_contract_bad.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
