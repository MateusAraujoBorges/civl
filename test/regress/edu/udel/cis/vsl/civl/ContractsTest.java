package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractsTest {
	/* *************************** Static Fields *************************** */

	private static String enableContract = "-mpiContract";

	private static File rootDir = new File(new File("examples"), "contracts");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void with() {
		assertTrue(ui.run(
				"verify -showModel=false -showTransitions=true -showSavedStates=false",
				// QUIET,
				filename("with.cvl")));
	}

	@Test
	public void with2() {
		assertTrue(ui.run(
				"verify -showModel=false -showTransitions=false -showSavedStates=false",
				// QUIET,
				filename("with2.cvl")));
	}

	@Test
	public void update() {
		assertTrue(
				ui.run("verify -showModel=false -showProgram=false -showTransitions=true -showSavedStates=true -quiet=false",
						QUIET, filename("update.cvl")));
	}

	@Test
	public void update2() {
		assertTrue(
				ui.run("verify -showModel=false -showProgram=false -showTransitions=true -showSavedStates=true -quiet=false",
						QUIET, filename("update2.cvl")));
	}

	@Test
	public void guardSE() {
		assertTrue(ui.run("verify -showProgram", // QUIET,
				filename("contractsMPI/simpleGuard.c")));
	}

	@Test
	public void mpiAgree() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract",
				filename("contractsMPI/simpleMpiAgree.c")));
	}

	@Test
	public void mpiRegion() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract=target",
				filename("contractsMPI/simpleMpiRegion.c")));
	}

	@Test
	public void mpiOffset() {
		assertTrue(ui.run("verify -input_mpi_nprocs=2 -mpiContract",
				filename("contractsMPI/simpleMpiOffset.c")));
	}

	// @Test
	// public void seq_sum() {
	// assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/sum.c")));
	// }
	//
	// @Test
	// public void pointers() {
	// assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers.c")));
	// }
	//
	// @Test
	// public void pointersBad() {
	// assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointersBad.c")));
	// }
	//
	// @Test
	// public void pointers2() {
	// assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers2.c")));
	// }
	//
	// @Test
	// public void pointers2Bad() {
	// assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers2Bad.c")));
	// }
	//
	// @Test
	// public void pointers2Bad2() {
	// assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers2Bad2.c")));
	// }
	//
	// @Test
	// public void pointers3() {
	// assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers3.c")));
	// }
	//
	// @Test
	// public void pointers3Bad() {
	// assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers3Bad.c")));
	// }
	//
	// @Test
	// public void pointers4() {
	// assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers4.c")));
	// }
	//
	// @Test
	// public void pointers4Bad() {
	// assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/pointers4Bad.c")));
	// }
	//
	// @Ignore
	// public void castVoidPointers() {
	// assertTrue(ui.run(VERIFY, " -errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/voidPointers.c")));
	// }
	//
	// @Test
	// public void globalPointers() {
	// assertTrue(ui.run(VERIFY, " -errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/globalPointers.c")));
	// }
	//
	// @Test
	// public void globalPointersBad() {
	// assertFalse(ui.run(VERIFY, " -errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/globalPointersBad.c")));
	// }
	//
	// @Ignore
	// public void loopInvariants() {
	// assertTrue(ui.run(VERIFY, " -errorBound=10", enableContract, QUIET,
	// filename("contractsSeq/loopInvariants.c")));
	// }
	//
	// /************************ concurrent section ***********************/
	// @Test
	// public void dummyMPITest() {
	// assertTrue(ui.run(VERIFY, " -input_mpi_nprocs=2 -errorBound=10",
	// enableContract, QUIET, filename("contractsMPI/dummyMpiTest.c")));
	// }
	//
	// @Test
	// public void simpleMPITest() {
	// assertTrue(ui
	// .run(VERIFY, "-input_mpi_nprocs=2 -errorBound=10",
	// enableContract, QUIET,
	// filename("contractsMPI/simpleMpiTest.c")));
	// }
	//
	// @Test
	// public void simpleMPITest3() {
	// assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=5 -errorBound=10",
	// enableContract, QUIET,
	// filename("contractsMPI/simpleMpiTest3.c")));
	// }
	//
	// @Test
	// public void broadcast() {
	// assertTrue(ui.run(VERIFY, " -input_mpi_nprocs=2 -errorBound=1",
	// enableContract, QUIET, filename("contractsMPI/broadcast.c")));
	// }
	//
	// @Test
	// public void broadcastBad() {
	// assertFalse(ui
	// .run(VERIFY, "-input_mpi_nprocs=4 -errorBound=1",
	// enableContract, QUIET,
	// filename("contractsMPI/broadcast_bad.c")));
	// }
	//
	// @Test
	// public void gather() {
	// assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=2 -errorBound=1",
	// enableContract, QUIET, filename("contractsMPI/gather.c")));
	// }
	//
	// @Test
	// public void gatherBad() {
	// assertFalse(ui.run(VERIFY, "-input_mpi_nprocs=4 -errorBound=1",
	// enableContract, QUIET, filename("contractsMPI/gather_bad.c")));
	// }
	//
	//
}
