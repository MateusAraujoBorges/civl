package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
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

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	/**
	 * This test reveals the limitation of CIVL: Cannot determine whether a
	 * non-concrete pointer is defined or not. This test case also appears in
	 * the CompareTest in the dev-test set.
	 */
	@Test
	public void unableExtractInt() {
		assertFalse(ui.run("verify", QUIET, filename("petscBad/ex2Driver.c"),
				filename("petscBad/ex2a.c")));
	}

	@Test
	public void simpleCompareTest() {
		assertTrue(ui.run("compare ", QUIET, "-spec",
				filename("simple/specDrive.c"), "-impl",
				filename("simple/implDriver.c"),
				filename("simple/implDependency1.c")));
	}

	@Test
	public void provesaCompareTest() {
		String provesaPath = rootDir.getPath() + "/provesa";
		String runtime_dense_reversePath = provesaPath
				+ "/runtime_dense_reverse";

		assertFalse(ui.run("compare ", QUIET, " -spec",
				filename("provesa/driver.c"), filename("provesa/tap_driver.c"),
				filename("provesa/o_fcn_bv.c"),
				"-impl -DADIC_DENSE_REVERSE -userIncludePath=" + provesaPath
						+ ":" + runtime_dense_reversePath,
				filename("provesa/driver.c"),
				filename("provesa/runtime_dense_reverse/ad_grad.c"),
				filename("provesa/runtime_dense_reverse/ad_tape.c"),
				filename("provesa/runtime_dense_reverse/ad_rev.c"),
				filename("provesa/adic_driver.c"),
				filename("provesa/head.cn.xb.pp.c")));
	}

	@Test
	public void typeAnalyzerException() {
		assertTrue(ui.run("compare", QUIET, "-spec",
				filename("type_dependency/spec.c"), "-impl",
				filename("type_dependency/impl.c")));
	}

	@Test
	public void unboundedAdderComparison() {
		assertTrue(ui.run("compare", "-loop", QUIET, "-spec -loop",
				filename("adder/ub_adder_spec.c"), "-impl -loop",
				"-input_mpi_nprocs=2", filename("adder/ub_adder_par.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
