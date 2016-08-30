package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class DirectedTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "direct");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	/* **************************** Test Methods *************************** */

	@Test
	public void itest() throws ABCException {
		assertTrue(ui.run("show", "-showProgram", "-direct="+filename("itest.direct"), filename("itest.c") ));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
