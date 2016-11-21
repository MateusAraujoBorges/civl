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

	@Test
	public void array_of_ptr() {
		assertTrue(ui.run(VERIFY, "-verbose", filename("array_of_ptr.c")));
	}

	@Test
	public void jan() {
		assertTrue(ui.run(VERIFY, filename("jan_example.c")));
	}

	@Test
	public void ptr_share() {
		assertFalse(ui.run(VERIFY, "-verbose", filename("ptr_share.c")));
	}

	@Test
	public void simple_omp_share() {
		assertTrue(ui.run(VERIFY, "-verbose", filename("simple_omp_share.c")));
	}

}
