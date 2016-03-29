package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class VerifyThisTest {
	private static File rootDir = new File(new File("examples"),
			"verifyThisProblems");
	
	private static UserInterface ui = new UserInterface();
	
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	
	// quantifiedComp.cvl
		@Test
		public void quantifiedComp() {
			assertTrue(ui.run(VERIFY, QUIET, filename("quantifiedComp.cvl")));
		}
}
