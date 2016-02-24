package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Test cases used to test -quiet option in the command eg. verify -quiet
 * filename
 * 
 * @author yihaoyan
 *
 */
public class QuietOptionTest {

	private static File rootDir1 = new File(new File("examples"), "concurrency");
	private static File rootDir2 = new File(new File("examples"),
			"compare/adder");
	private static UserInterface ui = new UserInterface();

	private static String filename1(String name) {
		return new File(rootDir1, name).getPath();
	}

	private static String filename2(String name) {
		return new File(rootDir2, name).getPath();
	}

	@Test
	public void adderRun() {
		assertTrue(ui.run(TestConstants.RUN, "-inputB=5", TestConstants.QUIET,
				TestConstants.NO_PRINTF, filename1("adder.cvl")));
	}

	@Test
	public void adderVerify() {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputB=5",
				TestConstants.NO_PRINTF, TestConstants.QUIET,
				filename1("adder.cvl")));
	}

	@Test
	public void adderBadVerify() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputB=5",
				TestConstants.NO_PRINTF, TestConstants.QUIET,
				filename1("adderBad.cvl")));
	}

	@Test
	public void adderBadReplay() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputB=5",
				TestConstants.NO_PRINTF, TestConstants.QUIET,
				filename1("adderBad.cvl")));

		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.QUIET,
				TestConstants.NO_PRINTF, filename1("adderBad.cvl")));
	}

	@Test
	public void adderCompare() {
		assertTrue(ui.run(TestConstants.COMPARE, "-inputNB=4",
				"-inputNPROCSB=2", TestConstants.QUIET,
				TestConstants.NO_PRINTF, TestConstants.IMPL,
				filename2("adder_par.cvl"), TestConstants.SPEC,
				filename2("adder_spec.cvl")));
	}

}
