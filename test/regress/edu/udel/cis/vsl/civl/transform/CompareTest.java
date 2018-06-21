package edu.udel.cis.vsl.civl.transform;

import static edu.udel.cis.vsl.civl.TestConstants.COMPARE;
import static edu.udel.cis.vsl.civl.TestConstants.IMPL;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.REPLAY;
import static edu.udel.cis.vsl.civl.TestConstants.SPEC;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void sumN() {
		assertTrue(ui.run(COMPARE, QUIET, "-inputN=10", SPEC,
				filename("sum", "sumNspec.cvl"), IMPL,
				filename("sum", "sumNimpl.cvl")));
	}

	@Test
	public void adder() {
		assertTrue(ui.run(COMPARE, NO_PRINTF,
				"-showProgram=false -input_mpi_nprocs_hi=2", "-inputNB=4", IMPL,
				QUIET, filename("adder", "adder_par.c"), SPEC,
				filename("adder", "adder_spec.c")));
	}

	@Test
	public void max() {
		assertFalse(ui.run(COMPARE, QUIET, NO_PRINTF, "-inputB=4 -min -spec",
				filename("max", "max.cvl"), filename("max", "max_seq.cvl"),
				"-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
				filename("max", "max.cvl"), filename("max", "max_par.cvl")));
		assertFalse(ui.run(REPLAY, QUIET, NO_PRINTF, "-spec",
				filename("max", "max.cvl"), filename("max", "max_seq.cvl"),
				"-impl", filename("max", "max.cvl"),
				filename("max", "max_par.cvl")));
	}

	@Test
	public void dotMpiPthreadsWeakScaling() {
		assertTrue(ui.run(COMPARE, QUIET, "-inputVECLEN=5", SPEC,
				"-inputMAXTHRDS=2",
				filename("dot", "mpithreads_threads_weak_scaling.c"), IMPL,
				"-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi_weak_scaling.c")));
	}

	@Test
	public void dotMpiSerialWeakScaling() {
		assertTrue(ui.run(COMPARE, NO_PRINTF, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi_weak_scaling.c")));
	}

	@Test
	public void dotPthreadsSerialWeakScaling() {
		assertTrue(ui.run(COMPARE, NO_PRINTF, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-inputMAXTHRDS=2",
				filename("dot", "mpithreads_threads_weak_scaling.c")));
	}

	@Test
	public void dotHybridSerialWeakScaling() {
		assertTrue(ui.run(COMPARE, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both_weak_scaling.c")));
	}

	@Test
	public void dotMpiHybridWeakScaling() {
		assertTrue(ui.run(COMPARE, QUIET, "-inputVECLEN=4 -input_mpi_nprocs=2",
				SPEC, filename("dot", "mpithreads_mpi_weak_scaling.c"), IMPL,
				"-inputMAXTHRDS=2",
				filename("dot", "mpithreads_both_weak_scaling.c")));
	}

	@Test
	public void outputfiles() {
		assertTrue(ui.run(COMPARE, QUIET, SPEC, filename("io", "out1.c"), IMPL,
				filename("io", "out2.c")));
	}

	@Test
	public void dotMpiPthreads() {
		assertTrue(ui.run(COMPARE, QUIET, "-inputVECLEN=5", SPEC,
				"-inputMAXTHRDS=2", filename("dot", "mpithreads_threads.c"),
				IMPL, "-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotHybrid() {
		assertTrue(ui.run(TestConstants.VERIFY, QUIET,
				"-inputVECLEN=1 -input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both.c")));
	}

	@Test
	public void dotMpiSerial() {
		// False because each process in the concurrent program is working on an
		// array with the same length of the serial one, then the total result
		// of the concurrent program is larger than the serial one.
		assertFalse(ui.run(COMPARE, NO_PRINTF, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-input_mpi_nprocs=2", filename("dot", "mpithreads_mpi.c")));

		assertFalse(ui.run(REPLAY, QUIET, NO_PRINTF, SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-input_mpi_nprocs=2", filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotPthreadsSerial() {
		// False because each process in the concurrent program is working on an
		// array with the same length of the serial one, then the total result
		// of the concurrent program is larger than the serial one.
		assertFalse(ui.run(COMPARE, NO_PRINTF, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-inputMAXTHRDS=2", filename("dot", "mpithreads_threads.c")));
	}

	@Test
	public void dotHybridSerial() {
		// False because each process in the concurrent program is working on an
		// array with the same length of the serial one, then the total result
		// of the concurrent program is larger than the serial one.
		assertFalse(ui.run(COMPARE, QUIET, "-inputVECLEN=5", SPEC,
				filename("dot", "mpithreads_serial.c"), IMPL,
				"-input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both.c")));
	}

	@Test
	public void dotMpiHybrid() {
		// False because each process is working on an array with the same size,
		// and the hybrid one has more processes than the mpi one, then the
		// result of the hybrid one is larger than just the mpi one.
		assertFalse(ui.run(COMPARE, QUIET, "-inputVECLEN=4 -input_mpi_nprocs=2",
				SPEC, filename("dot", "mpithreads_mpi.c"), IMPL,
				"-inputMAXTHRDS=2", filename("dot", "mpithreads_both.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
