package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
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
	public void pthread_driver_races_2() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_nvram_llseek_read_nvram_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_3() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_nvram_llseek_write_nvram_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_4() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_nvram_unlocked_ioctl_write_nvram_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_5() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_read_nvram_nvram_unlocked_ioctl_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_6() {
		assertFalse(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_read_nvram_write_nvram_false-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_7() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_configure_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_8() {
		assertFalse(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_current_false-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_9() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_get_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_10() {
		assertFalse(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_set_false-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_11() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_current_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_12() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_get_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_13() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_set_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_14() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_current_pc8736x_gpio_get_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_15() {
		assertFalse(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_current_pc8736x_gpio_set_false-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_16() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_get_pc8736x_gpio_set_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_17() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_change_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_18() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_configure_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_19() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_current_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_20() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_get_true-unreach-call.i")));
	}

	@Test
	public void pthread_driver_races_21() {
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_set_true-unreach-call.i")));
	}

	@Test
	public void pthread_complex_1() {
		// Expected error: VERIFIER_error(), but in fact other error
		assertFalse(ui.run("verify -svcomp17 ",
				filename("bounded_buffer_false-unreach-call.i")));
	}

	@Ignore
	@Test
	public void pthread_complex_2() {
		// Expected error: VERIFIER_error(), but in fact other error
		assertFalse(ui.run("verify -svcomp17",
				filename("elimination_backoff_stack_false-unreach-call.i")));
	}

	// stack_true_25 and pthread_finding_k_matches_true can't be true together,
	// due to the different requirement of the scale parameter
	@Ignore
	@Test
	public void stack_true_25() {
		// requires UNPP scale to be (2*pow(2)+1), which is also an odd number
		assertTrue(ui.run("verify -svcomp17",
				filename("25_stack_true-unreach-call.i")));
	}

	@Test
	public void pthread_finding_k_matches_true() {
		// requires UNPP scale to be an even number
		assertTrue(ui.run("verify -svcomp17",
				filename("pthread-finding-k-matches_true-unreach-call.i")));
	}

	@Test
	public void collect_symbolic_constant() {
		assertTrue(ui.run("verify -svcomp17 -timeout=20",
				filename("collectSymConstant.cvl")));
	}

	@Test
	public void indexer_true() throws ABCException {
		assertTrue(ui.run("verify", "-svcomp16", "-inputSIZE=2", "-inputMAX=4",
				"-inputNUM_THREADS=2", QUIET,
				filename("indexer_true-unreach-call.c")));
	}
}
