package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SideEffectsTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "sideEffects");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void postIncr() throws ABCException {
		assertTrue(ui.run("verify ", TestConstants.QUIET, filename("postIncr.cvl")));
	}

	@Test
	public void forLoopIncrSE() throws ABCException {
		assertTrue(ui.run("verify ", TestConstants.QUIET, filename("forLoopIncretSE.c")));
	}
	
	@Test
	public void strictInitTest() throws ABCException {
		assertTrue(ui.run("verify ", TestConstants.QUIET, 
				"-showProgram", filename("structInitSideEffect.c")));
	}
	
	@Test
	public void quantifiedExpressionTest() throws ABCException {
		assertFalse(ui.run("verify ", TestConstants.QUIET, 
				"-showProgram", filename("quantifiedSideEffects.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
