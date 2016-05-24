package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ModelBuilderTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "modelbuilder");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void arrayext() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayext.c")));
	}

	@Test
	public void arrayLambda() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayLambda.cvl")));
	}

	@Test
	public void forall() {
		assertTrue(ui.run(VERIFY, QUIET, filename("foralltest.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
