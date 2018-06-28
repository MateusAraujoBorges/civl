package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SvcompTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples", "pthread"),
			"svcomp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void intPointer() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("intPointer.c")));
	}

	@Test
	public void thread_local() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("threadLocal.c")));
	}

	@Test
	public void threadLocal() {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("threadLocal.c")));
	}

	@Test
	public void assume_with_disjuncts() {
		assertFalse(ui.run("verify  -svcomp16", TestConstants.QUIET,
				filename("assume_with_disjuncts.cvl")));
	}
}
