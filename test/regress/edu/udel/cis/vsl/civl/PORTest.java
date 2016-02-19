package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class PORTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "por");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void adder2() {
		assertTrue(ui.run("verify", "-inputN=4", TestConstants.QUIET, filename("adder2.cvl")));
	}

	@Test
	public void atomic0() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("atomic0.cvl")));
	}

	@Test
	public void atomic1() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("atomic1.cvl")));
	}

	@Test
	public void pointerShare() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("pointerShare.cvl")));
	}

	@Test
	public void pointerShare1() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("pointerShare1.cvl")));
	}

	@Test
	public void pointerShare2() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("pointerShare2.cvl")));
	}

	@Test
	public void trade3() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("trade3.cvl")));
	}

	@Test
	public void trade4() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("trade4.cvl")));
	}

	@Test
	public void guard1() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("guard1.cvl")));
	}

	@Test
	public void guard2() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("guard2.cvl")));
	}

	@Test
	public void waitTest() {
		assertFalse(ui.run("verify", TestConstants.QUIET, filename("wait.cvl")));
	}

	@Test
	public void loop() {
		assertFalse(ui.run(
				"verify -showAmpleSet -showTransitions=false -errorBound=4",
				TestConstants.QUIET, filename("loop.cvl")));
	}

	@Test
	public void loop2() {
		assertTrue(ui.run("verify -showAmpleSet -showTransitions=false",
				TestConstants.QUIET, filename("loop2.cvl")));
	}

	@Test
	public void loop3() {
		assertTrue(ui.run("verify -showAmpleSet -showTransitions=false",
				TestConstants.QUIET, filename("loop3.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
