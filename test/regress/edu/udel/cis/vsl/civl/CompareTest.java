package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CompareTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "compare");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	private static String filename(String name) {
		return filename(".", name);
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void sumN() {
		assertTrue(ui.run(TestConstants.COMPARE, "-inputN=10", TestConstants.QUIET,
				TestConstants.SPEC, filename("sumNspec.cvl"), 
				TestConstants.IMPL, filename("sumNimpl.cvl")));
	}

	@Test
	public void adder() {
		assertTrue(ui.run(TestConstants.COMPARE, TestConstants.SHOW_PROGRAM, TestConstants.QUIET,
				TestConstants.NO_PRINTF, "-inputNPROCSB=2", "-inputNB=4", 
				TestConstants.SPEC, filename("adder", "adder_par.cvl"), 
				TestConstants.IMPL, filename("adder", "adder_spec.cvl")));
	}

	@Test
	public void max() {
		ui.run(TestConstants.SHOW, filename("max", "max.cvl"), 
				filename("max", "max_seq.cvl"));
		// assertFalse(ui.run("compare -inputB=4 -min -spec",
		// filename("max", "max.cvl"), filename("max", "max_seq.cvl"),
		// "-impl -inputNPROCS=2 -inputBLOCK_SIZE=2",
		// filename("max", "max.cvl"), filename("max", "max_par.cvl")));
		// assertFalse(ui.run("replay -min -spec", filename("max", "max.cvl"),
		// filename("max", "max_seq.cvl"), "-impl",
		// filename("max", "max.cvl"), filename("max", "max_par.cvl")));
	}

	@Test
	public void dotMpiPthreads() {
		assertTrue(ui
				.run(TestConstants.COMPARE, TestConstants.NO_PRINTF, TestConstants.QUIET,
						"-inputVECLEN=5", TestConstants.SPEC,
						"-inputMAXTHRDS=2", filename("dot", "mpithreads_threads.c"),
						TestConstants.IMPL, "-input_mpi_nprocs=2",
						filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotMpiSerial() {
		assertFalse(ui.run(TestConstants.COMPARE, TestConstants.NO_PRINTF, TestConstants.QUIET,
				"-inputVECLEN=5", TestConstants.SPEC,
				filename("dot", "mpithreads_serial.c"),
				TestConstants.IMPL, "-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi.c")));
		
		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.SPEC, TestConstants.QUIET,
				filename("dot", "mpithreads_serial.c"),
				TestConstants.IMPL, "-input_mpi_nprocs=2",
				filename("dot", "mpithreads_mpi.c")));
	}

	@Test
	public void dotPthreadsSerial() {
		assertFalse(ui.run(TestConstants.COMPARE, TestConstants.NO_PRINTF,
				"-inputVECLEN=5", TestConstants.SPEC, TestConstants.QUIET,
				filename("dot", "mpithreads_serial.c"),
				TestConstants.IMPL, "-inputMAXTHRDS=2",
				filename("dot", "mpithreads_threads.c")));
	}

	@Test
	public void dotHybridSerial() {
		assertFalse(ui.run(TestConstants.COMPARE, TestConstants.NO_PRINTF, TestConstants.QUIET,
				"-inputVECLEN=5", TestConstants.SPEC,
				filename("dot", "mpithreads_serial.c"),
				TestConstants.IMPL, "-input_mpi_nprocs=2 -inputMAXTHRDS=2",
				filename("dot", "mpithreads_both.c")));
	}

	@Test
	public void outputfiles() {
		assertTrue(ui.run(TestConstants.COMPARE, TestConstants.QUIET,
				TestConstants.SPEC, filename("outputTest", "out1.c"),
				TestConstants.IMPL, filename("outputTest", "out2.c")));
	}

	@Test
	public void outputfile() {
		assertTrue(ui.run(TestConstants.COMPARE, TestConstants.QUIET,
				TestConstants.SPEC, filename("outputfile", "spec.c"),
				TestConstants.IMPL, filename("outputfile", "impl.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
