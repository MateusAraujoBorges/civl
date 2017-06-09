package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.REPLAY;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ReplayTest {
	private static File rootDir = new File("examples");

	private static UserInterface ui = new UserInterface();

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	// @Ignore
	@Test
	public void locksBad() throws ABCException {
		assertFalse(
				ui.run(VERIFY, QUIET, filename("concurrency/locksBad.cvl")));

		assertFalse(ui.run(REPLAY, "-showStates", QUIET,
				filename("concurrency/locksBad.cvl")));
	}
}
