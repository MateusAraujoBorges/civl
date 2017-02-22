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

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	// TODO: failing
	@Test
	public void typeAnalyzerException() {
		assertTrue(ui.run("compare", "-spec", filename("type_bad/spec.c"),
				"-impl", filename("type_bad/impl.c")));
	}

	/**
	 * This test reveals the limitation of CIVL: Cannot determine whether a
	 * non-concrete pointer is defined or not. This test case also appears in
	 * the CompareTest in the dev-test set.
	 */
	@Test
	public void unableExtractInt() {
		assertFalse(ui.run("verify", filename("petscBad/ex2Driver.c"),
				filename("petscBad/ex2a.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
