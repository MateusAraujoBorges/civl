package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

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
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("reorder_2_false-unreach-call.i")));
	}

	@Test
	public void stack_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("stack_true-unreach-call.i")));
	}

	// mix000_power.oepc_false-unreach-call.i
	@Test
	public void mix000_power() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("mix000_power.oepc_false-unreach-call.i")));
	}

	// mix000_power.opt_false-unreach-call.i
	@Test
	public void mix000_power_opt() throws ABCException {
		assertFalse(ui.run("verify", "-svcomp16", TestConstants.QUIET,
				filename("mix000_power.opt_false-unreach-call.i")));
	}
	
	@Test
	public void free_pthread_pool_test() {
		assertFalse(ui.run("verify", "-svcomp16", 
				filename("safestack_relacy_false-unreach-call.i")));
	}
}
