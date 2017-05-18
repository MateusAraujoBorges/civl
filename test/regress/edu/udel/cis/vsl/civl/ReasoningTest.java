package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ReasoningTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "reasoning");

	private static File cgDir = new File(new File("examples"), "cg");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String reasoningfilename(String name) {
		return new File(rootDir, name).getPath();
	}

	private static String cgfilename(String name) {
		return new File(cgDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void neqZero() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, reasoningfilename("neqZero.cvl")));
	}

	@Test
	public void evaluatePc() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, reasoningfilename("evaluatePc.cvl")));
	}

	@Test
	public void unsatClause() {
		assertTrue(ui.run(VERIFY, QUIET, reasoningfilename("unsatClause.c")));
	}

	@Test
	public void unsatClause2() {
		assertTrue(ui.run(VERIFY, QUIET, reasoningfilename("unsatClause2.c")));
	}

	@Test
	public void quantified() {
		assertTrue(ui.run(VERIFY, QUIET, reasoningfilename("quantified.cvl")));
	}

	@Test
	public void arraySliceHavoc() {
		assertTrue(ui.run(VERIFY, QUIET,
				reasoningfilename("arraySliceHavoc.cvl")));
	}

	@Test
	public void cg2Absolute() {
		assertTrue(
				ui.run(VERIFY, QUIET, TestConstants.NO_CHECK_DIVISION_BY_ZERO,
						"-inputN=2", cgfilename("cg.cvl")));
	}

	@Test
	public void cg5Probabilistic() {
		assertTrue(ui.run(VERIFY, QUIET, "-inputN=5", TestConstants.ENABLE_PROB,
				TestConstants.NO_CHECK_DIVISION_BY_ZERO, cgfilename("cg.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
