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
	public void linux() {
		ui.run("verify -svcomp16 -errorBound=10 -errorStateEquiv=FULL",
				filename(
						"linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_false-unreach-call.cil.out.c"));
	}

	@Test
	public void parport_false() {
		assertFalse(
				ui.run("verify -svcomp16 -showTransitions -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						filename("parport_false-unreach-call.i.cil.c")));
	}

	@Test
	public void floppy_false() {
		assertFalse(ui.run("verify -svcomp16", filename(
				"floppy_simpl4_false-unreach-call_true-termination.cil.c")));
	}

	@Test
	public void base_name() {
		assertFalse(ui.run(
				"verify -showModel=false -svcomp16 -errorBound=10 "
						+ "-errorStateEquiv=FULL",
				filename("basename_false-unreach-call.c")));
	}

	@Test
	public void stringLiteral() {
		assertTrue(ui.run("verify -showModel=false ",
				filename("stringLiteralIf.c")));
	}

	@Test
	public void Problem01() {
		assertFalse(
				ui.run("verify -svcomp16 -unpreproc -errorBound=1000 -errorStateEquiv=FULL",
						filename("Problem01_label15_false-unreach-call.c")));
	}

	@Test
	public void uniqueLoop() {
		assertFalse(
				ui.run("verify -svcomp16 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
						filename("unique_loop.c")));
	}

	@Test
	public void memtrack() {
		ui.run("verify -svcomp16 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
				filename("20051113-1.c_false-valid-memtrack.c"));
	}

	@Test
	public void gcd() {
		ui.run("verify -svcomp16 -showProgram=false -errorBound=10 -errorStateEquiv=FULL",
				filename("gcd_1_true-unreach-call.i"));
	}

	@Test
	public void uchar() {
		ui.run("verify ", filename("uchar.c"));
	}

	@Test
	public void svcompHeader() {
		ui.run("show -showProgram -svcomp16", filename("svcompHeader.i"));
	}

	@Test
	public void assumeTest() {
		ui.run("verify -showTransitions -svcomp16",
				filename("assume_with_disjuncts.c"));
	}

	@Test
	public void lorBug() {
		ui.run("verify -showTransitions ", filename("lorBug.cvl"));
	}

	@Test
	public void callocTest() {
		ui.run("verify -svcomp16 ",
				filename("race-2_2-container_of_false-unreach-call.i"));
	}

	@Test
	public void bitwise_op() {
		ui.run("verify -svcomp16 ", filename(
				"char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl_true-unreach-call.i"));
	}
}
