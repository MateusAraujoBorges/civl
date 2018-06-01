package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OmpOrphanTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProductOrphan() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=4",
				filename("dotProduct_orphan.c")));
	}

	@Test
	public void piOrphan() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-input_omp_thread_max=4",
				filename("pi_orphan.c")));
	}

	@Test
	public void sharedVarTest4() {
		// won't work even when move the function definition into the parallel
		// region.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				"-ompNoSimplify", filename("sharedVar4.cvl")));
	}

	@Test
	public void sharedVarTest2() {
		// This test will break when "-ompNoSimplify" option is not specified.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				TestConstants.QUIET, filename("sharedVar2.cvl")));
	}

	@Test
	public void sharedVarTest3() {
		// When disable omp simplifier, this test will fail.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				"-ompNoSimplify", TestConstants.QUIET,
				filename("sharedVar3.cvl")));
	}
}
