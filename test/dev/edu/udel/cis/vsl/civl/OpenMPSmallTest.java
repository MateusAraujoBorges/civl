package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Some simple OpenMP tests, all of which fail currently.
 * 
 * @author siegel
 */
public class OpenMPSmallTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	// TODO: failing
	/**
	 * This test will throw an CIVLUnimplementedFeatureException. Because
	 * currently, the OpenMP2CIVLWorker can only handle an array, whose element
	 * has a basic standard type.
	 */
	@Test
	public void array_of_ptr() {
		assertFalse(ui.run(VERIFY, filename("array_of_ptr.c")));
	}

	// TODO: failing
	/**
	 * This test will throw an CIVLUnimplementedFeatureException. Because
	 * currently, the OpenMP2CIVLWorker can only handle an array, whose element
	 * has a basic standard type.
	 */
	@Test
	public void jan() {
		assertFalse(ui.run(VERIFY, filename("jan_example.c")));
	}

	// TODO: failing
	/**
	 * The atomic is not transformed correctly,
	 * CIVL will report a race condition problem even though there is none.
	 */
	@Test
	public void ptr_share() {
		assertFalse(ui.run(VERIFY, "-input_omp_thread_max=4",
				filename("ptr_share.c")));
	}

	// TODO: failing
	/**
	 * The atomic is not transformed correctly,
	 * CIVL will report a race condition problem even though there is none.
	 */
	@Test
	public void simple_omp_share() {
		assertTrue(ui.run(VERIFY, "-input_omp_thread_max=4",
				filename("simple_omp_share.c")));
	}

}
