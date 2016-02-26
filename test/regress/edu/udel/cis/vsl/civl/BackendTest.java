package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.SHOW_SAVED_STATES;
import static edu.udel.cis.vsl.civl.TestConstants.SHOW_TRANSITIONS;
import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.errorBound;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class BackendTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "backend");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void printExpr() {
		assertTrue(ui.run(
				VERIFY, SHOW_SAVED_STATES, SHOW_TRANSITIONS,
				QUIET, filename("printExpr.cvl")));
	}

	@Test
	public void arrayWrite() {
		assertTrue(ui.run(
				VERIFY, SHOW_SAVED_STATES, SHOW_TRANSITIONS,
				QUIET, filename("arrayWrite.cvl")));
	}

	@Test
	public void showTrans() {
		assertTrue(ui.run(VERIFY, SHOW_TRANSITIONS, QUIET, 
				filename("showTrans.cvl")));
	}

	@Test
	public void sizeOfTypes() {
		assertTrue(ui.run(VERIFY, SHOW_TRANSITIONS, QUIET, 
				filename("sizeOfTypes.c")));
	}

	@Test
	public void returnNull() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2),
				NO_PRINTF, QUIET, 
				filename("returnNull.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
