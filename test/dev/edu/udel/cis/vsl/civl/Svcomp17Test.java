package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class Svcomp17Test {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "svcomp17");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void uchar() {
		ui.run("verify ", TestConstants.QUIET, filename("uchar.c"));
	}

	@Test
	public void uniqueLoop() {
		assertFalse(
				ui.run("verify -svcomp17 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						TestConstants.QUIET, filename("unique_loop.c")));
	}
	
	@Test
	public void stringLiteral() {
		assertTrue(ui.run("verify -showModel=false ", TestConstants.QUIET,
				filename("stringLiteralIf.c")));
	}
	
	@Test
	public void assumeTest() {
		ui.run("verify -svcomp17", TestConstants.QUIET,
				filename("assume_with_disjuncts.c"));
	}
	
	@Test
	public void lorBug() {
		ui.run("verify -showTransitions=false ", TestConstants.QUIET,
				filename("lorBug.cvl"));
	}
	
	@Test
	public void unnamed_field() {
		assertTrue(ui.run("verify", TestConstants.QUIET,
				filename("unnamedField.c")));
	}

	// *************** Success CIVL 3826, ABC 1384 *****************

	@Test
	public void floppy_false() {
		assertFalse(ui.run("verify -svcomp17", TestConstants.QUIET, filename(
				"floppy_simpl4_false-unreach-call_true-termination.cil.c")));
	}

	@Test
	public void memtrack() {
		assertFalse(
				ui.run("verify -svcomp17 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						TestConstants.QUIET,
						filename("20051113-1.c_false-valid-memtrack.c")));
	}

	@Test
	public void callocTest() {
		assertFalse(ui.run("verify -svcomp17 ", TestConstants.QUIET,
				filename("race-2_2-container_of_false-unreach-call.i")));
	}

	// *************** Failed CIVL 3826, ABC 1384 *****************

	@Test
	public void svcompHeader() {
		// Can't find the header..
		ui.run("show -svcomp17", filename("svcompHeader.i"));
	}

	@Test
	public void int2pointerOnInputs() {
		// DEREFERENCE violation at int2pointerOnSymConst.cvl:4.2-5 "q[0]"
		ui.run("verify -svcomp17", filename("int2pointerOnSymConst.cvl"));
	}

	@Test
	public void linux() {
		// Syntax error: Can't find the definition for variable __this_module
		assertFalse(ui.run(
				"verify -svcomp17 -errorBound=10 -errorStateEquiv=FULL",
				filename(
						"linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_false-unreach-call.cil.out.c")));
		assertFalse(true);
	}

	@Test
	public void parport_false() {
		// HomogeneousExpression cannot be cast to ReferenceExpression
		assertFalse(
				ui.run("verify -svcomp17 -showTransitions -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						filename("parport_false-unreach-call.i.cil.c")));
	}

	@Test
	public void base_name() {
		// Error: Redeclaration of entity with incompatible type: sleep
		assertFalse(ui.run(
				"verify -showModel=false -svcomp17 -errorBound=10 "
						+ "-errorStateEquiv=FULL",
				filename("basename_false-unreach-call.c")));
		assertFalse(true);
	}

	@Test
	public void Problem01() {
		// False Positive (Should report violation)
		assertFalse(
				ui.run("verify -svcomp17 -unpreproc -errorBound=1000 -errorStateEquiv=FULL",
						filename("Problem01_label15_false-unreach-call.c")));
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
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_set_true-unreach-call.i")));
	}

	@Test
	public void char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl_true() {
		// Error: Anonymous struct or union.
		assertTrue(ui.run("verify -svcomp17", filename(
				"char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl_true-unreach-call.i")));
	}
}
