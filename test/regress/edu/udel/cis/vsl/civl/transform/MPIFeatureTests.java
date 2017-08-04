package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class MPIFeatureTests {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"mpi/mpiFeature");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dynamicBuffer() {
		assertTrue(ui.run("verify -input_mpi_nprocs=3", "-deadlock=potential",
				TestConstants.QUIET, filename("dy_buf_good.c")));
	}

	@Test
	public void dynamicBufferBad() {
		assertFalse(ui.run("verify -input_mpi_nprocs=3", "-deadlock=potential",
				TestConstants.QUIET, filename("dy_buf_bad.c")));
		assertFalse(ui.run("replay ", "-deadlock=potential",
				TestConstants.QUIET, filename("dy_buf_bad.c")));
	}

	@Test
	public void matmatCompareBad() {
		assertFalse(ui.run("compare -input_mpi_nprocs=2", TestConstants.QUIET,
				"-impl", filename("matmat_mw_bad.c"), "-spec",
				filename("matmat_spec.c")));
	}

	@Test
	public void matmatCompare() {
		assertTrue(ui.run("compare -input_mpi_nprocs=2 -collectHeaps=false",
				TestConstants.QUIET, "-impl", filename("matmat_mw_good.c"),
				"-spec", filename("matmat_spec.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
