package edu.udel.cis.vsl.civl.transform;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.OMP_NO_SIMP;
import static edu.udel.cis.vsl.civl.TestConstants.OMP_THREAD_TWO;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OpenMP2CIVLTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");
	private static File simpleDir = new File(rootDir, "simple");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	private static String filename(File dir, String fname) {
		return new File(dir, fname).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProduct1() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_NO_SIMP, OMP_THREAD_TWO, QUIET,
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProduct1Simplify() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_THREAD_TWO, QUIET,
				filename("dotProduct1.c")));
	}

	@Test
	public void dotProductCritical() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_NO_SIMP, OMP_THREAD_TWO, QUIET,
				filename("dotProduct_critical.c")));
	}

	@Test
	public void dotProductCriticalSimplify() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_THREAD_TWO, QUIET,
				filename("dotProduct_critical.c")));
	}

	@Test
	public void matProduct1Simplify() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_THREAD_TWO, QUIET,
				filename("matProduct1.c")));
	}

	@Test
	public void parallelfor() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_NO_SIMP, OMP_THREAD_TWO, QUIET,
				filename("parallelfor.c")));
	}

	@Test
	public void parallelforSimplify() {
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_THREAD_TWO, QUIET,
				filename("parallelfor.c")));
	}

	@Test
	public void sharedVarTest1() {
		// after moving the function definition into the parallel region, this
		// example will work.
		assertTrue(ui.run(VERIFY, NO_PRINTF, OMP_THREAD_TWO, QUIET,
				filename("sharedVar1.cvl")));
	}

	@Test
	public void omp_reduce() {
		assertTrue(ui.run(VERIFY, OMP_NO_SIMP, OMP_THREAD_TWO, QUIET,
				filename(simpleDir, "omp_reduce.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
