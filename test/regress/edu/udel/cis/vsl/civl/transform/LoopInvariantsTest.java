package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LoopInvariantsTest {
	private static File rootDir = new File(new File("examples"),
			"loop_invariants");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void arrayEquals() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayEquals.cvl")));
	}

	@Test
	public void arrayEquals2() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayEquals2.cvl")));
	}

	@Test
	public void arrayEqualsNoReturn() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayEqualsNoReturn.cvl")));
	}

	@Test
	public void arrayEqualsNoReturnBad() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayEqualsNoReturn-bad.cvl")));
	}

	@Test
	public void arrayZeroes1d() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayZeroes1d.cvl")));
	}

	@Test
	public void arrayZeroes1dBad() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayZeroes1d-bad.cvl")));
	}

	@Test
	public void arrayZeroes2d() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayZeroes2d.cvl")));
	}

	@Test
	public void arrayZeroes2dBadAssert() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayZeroes2d-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dBadInvariants() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("arrayZeroes2d-bad_invariants.cvl")));
	}
	@Ignore
	public void max() {
		assertTrue(ui.run("verify", "-showTransitions", filename("max.cvl")));
	}

	@Test
	public void maxBadAssert() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("max-bad_assert.cvl")));
	}

	@Test
	public void maxBadInvariants() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("max-bad_invariants.cvl")));
	}

	@Ignore
	public void selectSort() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("selectSort.cvl")));
	}
	@Test
	public void selectSortBadAssert() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				TestConstants.errorBound(3),
				filename("selectSort-bad_assert.cvl")));
	}

	@Test
	public void selectSortBadInvariants() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("selectSort-bad_invariants.cvl")));
	}

	@Test
	public void selectSortBadThink() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("selectSort-bad_think.cvl")));
	}

	@Test
	public void twoLoopsUnreachable() {
		assertTrue(ui.run("verify", "-collectSymbolicConstants=true",
				filename("twoLoops.cvl")));
	}

	@Test
	public void twoLoopsBad() {
		assertFalse(ui.run("verify", "-collectSymbolicConstants=true",
				filename("twoLoops2.cvl")));
	}
}
