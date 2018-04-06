package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SlowLoopInvariantsWithAssignsTest2 {
	private static File rootDir = new File(new File("examples"),
			"loop_invariants/");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void foVeOOS_max() {
		assertTrue(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true",
				filename("foVeOOS/max/max.cvl")));
	}

	@Test
	public void foVeOOS_maxBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true",
				filename("foVeOOS/max/max-bad_assert.cvl")));
	}

	@Test
	public void foVeOOS_maxBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true",
				filename("foVeOOS/max/max-bad_invariant.cvl")));
	}

	@Test
	public void foVeOOS_duplets() {
		assertTrue(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true",
				filename("foVeOOS/twoEqualElements/two_equal_elements.cvl")));
	}

	@Test
	public void foVeOOS_dupletsBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true", filename(
						"foVeOOS/twoEqualElements/two_equal_elements-bad_assert.cvl")));
	}

	@Test
	public void foVeOOS_dupletsBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET,
				"-collectSymbolicConstants=true", filename(
						"foVeOOS/twoEqualElements/two_equal_elements-bad_invariant.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
		System.gc();
	}
}
