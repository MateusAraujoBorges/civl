package edu.udel.cis.vsl.civl;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import org.junit.AfterClass;
import org.junit.Test;

import java.io.File;

import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertTrue;

public class StatisticalTests {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "statistical");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private void check(String name) {
		assertTrue(ui.run(VERIFY, /*QUIET*/ "-debug", "-statistical", filename(name)));
//		assertTrue(ui.run(VERIFY, /*QUIET*/ "-debug", filename(name)));
	}

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dumb() {
		check("dumb.cvl");
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
