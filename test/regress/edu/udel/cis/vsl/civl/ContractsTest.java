package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import jdk.nashorn.internal.ir.annotations.Ignore;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ContractsTest {
	/* *************************** Static Fields *************************** */

	private static String enableContract = "-mpiContract";

	private static File rootDir = new File(new File("examples"), "experimental");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void seq_sum() {
		assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/sum.c")));
	}

	@Test
	public void pointers() {
		assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers.c")));
	}

	@Test
	public void pointersBad() {
		assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointersBad.c")));
	}

	@Test
	public void pointers2() {
		assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers2.c")));
	}

	@Test
	public void pointers2Bad() {
		assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers2Bad.c")));
	}

	@Test
	public void pointers2Bad2() {
		assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers2Bad2.c")));
	}

	@Test
	public void pointers3() {
		assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers3.c")));
	}

	@Test
	public void pointers3Bad() {
		assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers3Bad.c")));
	}

	@Test
	public void pointers4() {
		assertTrue(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers4.c")));
	}

	@Test
	public void pointers4Bad() {
		assertFalse(ui.run(VERIFY, "-errorBound=10", enableContract, QUIET,
				filename("sequential/pointers4Bad.c")));
	}

	@Ignore
	public void castVoidPointers() {
		assertTrue(ui.run(VERIFY, " -errorBound=10", enableContract, QUIET,
				filename("sequential/voidPointers.c")));
	}

	@Test
	public void globalPointers() {
		assertTrue(ui.run(VERIFY, "  -errorBound=10", enableContract, QUIET,
				filename("sequential/globalPointers.c")));
	}

	@Test
	public void globalPointersBad() {
		assertFalse(ui.run(VERIFY, "  -errorBound=10", enableContract, QUIET,
				filename("sequential/globalPointersBad.c")));
	}

	/************************ concurrent section ***********************/
	@Test
	public void dummyMPITest() {
		assertTrue(ui.run(VERIFY, " -input_mpi_nprocs=2 -errorBound=10",
				enableContract, QUIET, filename("sequential/dummyMpiTest.c")));
	}

	@Test
	public void simpleMPITest() {
		assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=2 -errorBound=10",
				enableContract, QUIET, filename("sequential/simpleMpiTest.c")));
	}

	@Test
	public void simpleMPITest3() {
		assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=5 -errorBound=10",
				enableContract, QUIET, filename("sequential/simpleMpiTest3.c")));
	}

	@Test
	public void broadcast() {
		assertTrue(ui.run(VERIFY, " -input_mpi_nprocs=2 -errorBound=1",
				enableContract, QUIET, filename("sequential/broadcast.c")));
	}

	@Test
	public void broadcastBad() {
		assertFalse(ui.run(VERIFY, "-input_mpi_nprocs=4 -errorBound=1",
				enableContract, QUIET, filename("sequential/broadcast_bad.c")));
	}

	@Test
	public void gather() {
		assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=2 -errorBound=1",
				enableContract, QUIET, filename("sequential/gather.c")));
	}

	@Test
	public void gatherBad() {
		assertFalse(ui.run(VERIFY, "-input_mpi_nprocs=4 -errorBound=1",
				enableContract, QUIET, filename("sequential/gather_bad.c")));
	}

	@Test
	public void allgather() {
		assertTrue(ui.run(VERIFY, "-input_mpi_nprocs=2 -errorBound=1",
				enableContract, QUIET, filename("sequential/allgather.c")));
	}
}
