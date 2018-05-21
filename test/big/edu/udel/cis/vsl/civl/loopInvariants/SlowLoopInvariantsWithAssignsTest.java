package edu.udel.cis.vsl.civl.loopInvariants;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SlowLoopInvariantsWithAssignsTest {
	private static File rootDir = new File(new File("examples"),
			"loop_invariants/loop_assigns_given");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */
	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void arrayEquals() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEquals.cvl")));
	}

	@Test
	public void arrayEqualsBug() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEquals-bug.cvl")));
	}

	@Test
	public void arrayEqualsEarlyReturn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEquals_early_return.cvl")));
	}

	@Test
	public void arrayEquals2() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEquals2.cvl")));
	}

	@Test
	public void arrayEqualsNoReturn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEqualsNoReturn.cvl")));
	}

	@Test
	public void arrayEqualsNoReturnBadImpl() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEqualsNoReturn-bad_impl.cvl")));
	}

	@Test
	public void arrayEqualsNoReturnBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayEqualsNoReturn-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes1d() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes1d.cvl")));
	}

	@Test
	public void arrayZeroes1dBad() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes1d-bad.cvl")));
	}

	@Test
	public void arrayZeroes2d() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("arrayZeroes2d.cvl")));
	}

	@Test
	public void arrayZeroes2dColumn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d_column.cvl")));
	}

	@Test
	public void arrayZeroes2d2Columns() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d_2columns.cvl")));
	}

	@Test
	public void arrayZeroes2dColumnPreserve() {
		assertTrue(ui.run("verify", "-loop -showTransitions",
				filename("arrayZeroes2d_2columns_preserve.cvl")));
	}

	@Test
	public void arrayZeroes2d2ColumnsPreserve() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("arrayZeroes2d_2columns_preserve.cvl")));
	}

	@Test
	public void arrayZeroes2d2ColumnsPreserveBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("arrayZeroes2d_2columns_preserve-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dColumnBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d_column-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dColumnBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d_column-bad_invariant.cvl")));
	}

	@Test
	public void arrayZeroes2dBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("arrayZeroes2d-bad_invariants.cvl")));
	}
	@Ignore
	public void max() {
		assertTrue(ui.run("verify", TestConstants.QUIET, filename("max.cvl")));
	}

	@Test
	public void maxBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("max-bad_assert.cvl")));
	}

	@Test
	public void maxBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("max-bad_invariants.cvl")));
	}

	@Test
	public void insertionSort() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("insertSort.cvl")));
	}

	@Test
	public void insertionSortBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("insertSort-bad_assert.cvl")));
	}

	@Test
	public void insertionSortBadAssert2() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("insertSort-bad_assert2.cvl")));
	}

	@Test
	public void selectSort() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("selectSort.cvl")));
	}

	@Test
	public void selectSortBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				TestConstants.errorBound(3),
				filename("selectSort-bad_assert.cvl")));
	}

	@Test
	public void selectSortBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("selectSort-bad_invariants.cvl")));
	}

	@Test
	public void selectSortBadThink() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("selectSort-bad_think.cvl")));
	}

	@Test
	public void twoLoopsUnreachable() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("twoLoops.cvl")));
	}

	@Test
	public void twoLoopsBad() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("twoLoops2.cvl")));
	}

	@Test
	public void summation() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("summation.cvl")));
	}

	@Test
	public void summationBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("summation-bad_invariant.cvl")));
	}

	@Test
	public void summationBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop",
				filename("summation-bad_assert.cvl")));
	}

	@Test
	public void JanLoop1st() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_1st_loop.cvl")));
	}

	@Test
	public void JanLoop1stBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_1st_loop-bad_assert.cvl")));
	}

	@Test
	public void JanLoop1stBadAssigns() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../Jans_example/invariant_1st_loop-bad_assigns.cvl")));
	}

	@Test
	public void JanLoop2nd() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_2nd_loop.cvl")));
	}

	@Test
	public void JanLoop2ndBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_2nd_loop_bad-assert.cvl")));
	}

	@Test
	public void JanLoop2ndBadAssigns() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../Jans_example/invariant_2nd_loop_bad-assigns.cvl")));
	}

	@Test
	public void JanLoop3rd() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_3rd_loop.cvl")));
	}

	@Test
	public void JanLoop3rdBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET,
				filename("../Jans_example/invariant_3rd_loop-bad_assert.cvl")));
	}

	@Test
	public void JanLoop3rdBadAssigns() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../Jans_example/invariant_3rd_loop-bad_assigns.cvl")));
	}

	@Test
	public void relaxedPrefix() {
		assertTrue(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../verifyThisNB/relaxedPrefix/relaxedPrefix_loop.cvl")));
	}

	@Test
	public void relaxedPrefixWeak() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../verifyThisNB/relaxedPrefix/relaxedPrefix_loop-bad_weak.cvl")));
	}

	@Test
	public void relaxedPrefixWeak2() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../verifyThisNB/relaxedPrefix/relaxedPrefix_loop-bad_weak2.cvl")));
	}

	@Test
	public void relaxedPrefixBadAssert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../verifyThisNB/relaxedPrefix/relaxedPrefix_loop-bad_assert.cvl")));
	}

	@Test
	public void relaxedPrefixWeak4Assert() {
		assertFalse(ui.run("verify", "-loop", TestConstants.QUIET, filename(
				"../verifyThisNB/relaxedPrefix/relaxedPrefix_loop-bad_weak4assert.cvl")));
	}

	@Test
	public void sort() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/sort_deductive.cvl")));
	}

	@Test
	public void sortBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/sort-bad_invariant.cvl")));
	}

	@Test
	public void sortBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/sort-bad_assert.cvl")));
	}

	@Test
	public void lrsBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/lrs-bad_invariant.cvl")));
	}

	@Test
	public void lrsBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/lrs-bad_assert.cvl")));
	}

	@Test
	public void lrs() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/lrs_deductive.cvl ")));
	}

	@Test
	public void pairInsertion() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/pairInsertSort/pairInsertSort_partial.cvl")));
	}

	@Test
	public void pairInsertionBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/pairInsertSort/pairInsertSort_partial-bad_assert.cvl")));
	}

	@Ignore // requires why3 with TIMEOUT > 10 seconds
	public void lcp2() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop", filename(
				"../verifyThisNB/longestRepeatedSubstring/lcp2.cvl ")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
		System.gc();
	}
}
