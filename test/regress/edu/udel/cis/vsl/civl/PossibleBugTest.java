package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PossibleBugTest {
	private static File rootDir = new File(new File("examples"), "possibleBug");

	private static UserInterface ui = new UserInterface();
	
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	
	@Test
	public void classCastException1() {
		assertTrue(ui.run("verify", filename("classCastException.cvl")));
	}
}
