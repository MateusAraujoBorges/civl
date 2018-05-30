package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OpenMP2CIVLTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProduct1() {
		assertTrue(ui.run("verify ", NO_PRINTF, "-ompNoSimplify",
				"-input_omp_thread_max=2", TestConstants.QUIET,
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProduct1Simplify() {
		assertTrue(ui.run("verify ", NO_PRINTF, "-input_omp_thread_max=2",
				TestConstants.QUIET, filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("verify ", NO_PRINTF, "-ompNoSimplify",
				"-input_omp_thread_max=2", TestConstants.QUIET,
				filename("dotProduct_critical.c")));
	}

	@Test
	public void dotProductCriticalSimplify() {
		assertTrue(ui.run("verify ", NO_PRINTF, "-input_omp_thread_max=2",
				TestConstants.QUIET, filename("dotProduct_critical.c")));
	}

	@Test
	public void matProduct1Simplify() {
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				TestConstants.QUIET, filename("matProduct1.c")));
	}

	@Test
	public void parallelfor() {
		assertTrue(ui.run("verify", NO_PRINTF, "-ompNoSimplify",
				"-input_omp_thread_max=2", TestConstants.QUIET,
				filename("parallelfor.c")));
	}

	@Test
	public void parallelforSimplify() {
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				TestConstants.QUIET, filename("parallelfor.c")));
	}

	@Test
	public void sharedVarTest1() {
		// after moving the function definition into the parallel region, this
		// example will work.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				filename("sharedVar1.cvl")));
	}

	@Test
	public void sharedVarTest2() {
		// work when mannually change, maybe something wrong with the current
		// orphan transformer.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				"-showProgram",
				// "-ompNoSimplify",
				filename("sharedVar2.cvl")));
	}

	@Test
	public void sharedVarTest3() {
		// will work when copy the function definition into parallel region, but
		// why this is a failing test?
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				"-showProgram", filename("sharedVar3.cvl")));
	}

	@Test
	public void sharedVarTest4() {
		// won't work even when move the function definition into the parallel
		// region.
		assertTrue(ui.run("verify", NO_PRINTF, "-input_omp_thread_max=2",
				"-ompNoSimplify", "-showProgram", filename("sharedVar4.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
