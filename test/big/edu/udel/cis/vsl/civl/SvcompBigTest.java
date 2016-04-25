package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SvcompBigTest {
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
	public void mix023_tso() throws ABCException {
		assertFalse(ui.run("verify -showProgram=false", "-svcomp16",
				TestConstants.QUIET,
				filename("mix023_tso.opt_false-unreach-call.i")));
	}

	// reorder_2_false-unreach-call.i
	@Test
	public void reorder_2_false() throws ABCException {
		assertFalse(ui
				.run("verify", "-svcomp16 -showProgram=false",
						TestConstants.QUIET,
						filename("reorder_2_false-unreach-call.i")));
	}
}
