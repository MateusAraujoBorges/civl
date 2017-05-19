package edu.udel.cis.vsl.civl.transform;

import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractTest {
	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "contracts");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void broadcast() {
		assertTrue(
				ui.run(VERIFY, "-input_mpi_nprocs=2", "-mpiContract=broadcast",
						TestConstants.QUIET, "-collectSymbolicConstants=true",
						filename("/contractsMPI/broadcast.c")));
	}

	@Test
	public void broadcastBad() {
		assertFalse(
				ui.run(VERIFY, "-input_mpi_nprocs=2", "-mpiContract=broadcast",
						TestConstants.QUIET, "-collectSymbolicConstants=true",
						filename("/contractsMPI/broadcast_bad.c")));
	}
}
