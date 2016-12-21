package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class Svcomp17PthreadsTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "svcomp17");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void callocTest() {
		assertFalse(ui.run("verify -svcomp17 ", TestConstants.QUIET,
				filename("race-2_2-container_of_false-unreach-call.i")));
	}

	// *************** Failed CIVL 3826, ABC 1384 *****************

	@Test
	public void int2pointerOnInputs() {
		// DEREFERENCE violation at int2pointerOnSymConst.cvl:4.2-5 "q[0]"
		ui.run("verify -svcomp17", filename("int2pointerOnSymConst.cvl"));
	}

	@Test
	public void gcd() {
		// False Negative (Should report no violation)
		assertTrue(
				ui.run("verify -svcomp17 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						filename("gcd_1_true-unreach-call.i")));
	}

	@Test
	public void bitwise_op1() {
		// Error: Anonymous struct or union.
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_configure_true-unreach-call.i")));
	}

	@Test
	public void bitwise_op2() {
		// Error: Anonymous struct or union.
		assertTrue(ui.run("verify -svcomp17 -debug=false", filename(
				"char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_set_true-unreach-call.i")));
	}

	@Test
	public void char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl_true() {
		// Error: Anonymous struct or union.
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl_true-unreach-call.i")));
	}
}
