package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

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
				TestConstants.VERIFY, TestConstants.NO_SHOW_PROGRAM, 
				TestConstants.SHOW_SAVED_STATES, TestConstants.SHOW_TRANSITIONS,
				TestConstants.QUIET, filename("printExpr.cvl")));
	}

	@Test
	public void arrayWrite() {
		assertTrue(ui.run(
				TestConstants.VERIFY, TestConstants.NO_SHOW_PROGRAM,
				TestConstants.SHOW_SAVED_STATES, TestConstants.SHOW_TRANSITIONS,
				TestConstants.QUIET, filename("arrayWrite.cvl")));
	}

	@Test
	public void showTrans() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_SHOW_PROGRAM,
				TestConstants.SHOW_TRANSITIONS, TestConstants.QUIET, 
				filename("showTrans.cvl")));
	}

	@Test
	public void sizeOfTypes() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_SHOW_PROGRAM,
				TestConstants.SHOW_TRANSITIONS, TestConstants.QUIET, 
				filename("sizeOfTypes.c")));
	}

	@Test
	public void returnNull() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(2),
				TestConstants.NO_PRINTF, TestConstants.QUIET, 
				filename("returnNull.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
