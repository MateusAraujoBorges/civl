package edu.udel.cis.vsl.civl.loopInvariants;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SlowLoopInvariantsNoAssignsTest {

	private static File rootDir = new File(new File("examples"),
			"loop_invariants/loop_assigns_gen");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Test
	public void arrayEquals() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEquals.cvl")));
	}

	@Ignore
	public void arrayEqualsBug() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEquals-bug.cvl")));
	}

	@Ignore
	public void arrayEqualsEarlyReturn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEquals_early_return.cvl")));
	}

	@Test
	public void arrayEquals2() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEquals2.cvl")));
	}

	@Test
	public void arrayEqualsNoReturn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEqualsNoReturn.cvl")));
	}

	@Test
	public void arrayEqualsNoReturnBadImpl() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEqualsNoReturn-bad_impl.cvl")));
	}

	@Ignore
	public void arrayEqualsNoReturnBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayEqualsNoReturn-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes1d() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes1d.cvl")));
	}

	@Test
	public void arrayZeroes1dBad() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes1d-bad.cvl")));
	}

	@Test
	public void arrayZeroes2d() {
		assertTrue(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("arrayZeroes2d.cvl")));
	}

	@Test
	public void arrayZeroes2dColumn() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d_column.cvl")));
	}

	@Test
	public void arrayZeroes2d2Columns() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d_2columns.cvl")));
	}

	@Ignore
	public void arrayZeroes2dColumnPreserve() {
		assertTrue(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("arrayZeroes2d_2columns_preserve.cvl")));
	}

	@Ignore
	public void arrayZeroes2d2ColumnsPreserve() {
		assertTrue(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("arrayZeroes2d_2columns_preserve.cvl")));
	}

	@Test
	public void arrayZeroes2d2ColumnsPreserveBadAssert() {
		assertFalse(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("arrayZeroes2d_2columns_preserve-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dColumnBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d_column-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dColumnBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d_column-bad_invariant.cvl")));
	}

	@Test
	public void arrayZeroes2dBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d-bad_assert.cvl")));
	}

	@Test
	public void arrayZeroes2dBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("arrayZeroes2d-bad_invariants.cvl")));
	}
	@Ignore
	public void max() {
		assertTrue(ui.run("verify", TestConstants.QUIET, filename("max.cvl")));
	}

	@Test
	public void foVeOOS_max() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("max2.cvl")));
	}

	@Test
	public void maxBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("max-bad_assert.cvl")));
	}

	@Test
	public void maxBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("max-bad_invariants.cvl")));
	}

	@Test
	public void selectSort() {
		assertTrue(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("selectSort.cvl")));
	}

	@Test
	public void selectSortBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				TestConstants.errorBound(3),
				filename("selectSort-bad_assert.cvl")));
	}

	@Test
	public void selectSortBadInvariants() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("selectSort-bad_invariants.cvl")));
	}

	@Test
	public void selectSortBadThink() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("selectSort-bad_think.cvl")));
	}

	@Test
	public void twoLoopsUnreachable() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("twoLoops.cvl")));
	}

	@Test
	public void twoLoopsBad() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("twoLoops2.cvl")));
	}

	@Test
	public void summation() {
		assertTrue(ui.run("verify", "-loop=true", TestConstants.QUIET,
				filename("summation.cvl")));
	}

	@Test
	public void summationBadInvariant() {
		assertFalse(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("summation-bad_invariant.cvl")));
	}

	@Test
	public void summationBadAssert() {
		assertFalse(ui.run("verify", TestConstants.QUIET,
				"-loop=true", filename("summation-bad_assert.cvl")));
	}

	@Test
	public void relaxPrefix() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("relaxedPrefix_loop.cvl")));
	}

	@Ignore // Need why3 with timeout > 15 seconds
	public void lcp2() {
		assertTrue(ui.run("verify", TestConstants.QUIET, "-loop=true",
				filename("lcp2.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
		System.gc();
	}
}
