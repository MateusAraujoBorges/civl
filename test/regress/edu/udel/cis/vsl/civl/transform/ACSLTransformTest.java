package edu.udel.cis.vsl.civl.transform;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ACSLTransformTest {
	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"),
			"ACSLTransformation");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* *************************** Test Methods **************************** */

	@Test
	public void predicate() {
		assertTrue(ui.run("show", QUIET, filename("predicate.cvl")));
	}

	@Test
	public void predicateUnsupportFormal() {
		assertFalse(ui.run("show", QUIET,
				filename("predicate-unsupport_formal.cvl")));
	}

	@Test
	public void predicateUnsupportFormal2() {
		assertFalse(ui.run("show", QUIET,
				filename("predicate-unsupport_formal2.cvl")));
	}

	@Test
	public void predicateUnsupportFormal3() {
		assertFalse(ui.run("show", QUIET,
				filename("predicate-unsupport_formal3.cvl")));
	}

	@Test
	public void predicateBadStateDepend() {
		assertFalse(ui.run("verify", QUIET,
				filename("predicate-bad_state_depend.cvl ")));
	}

	@Test
	public void predicateBadDeclTwice() {
		assertFalse(ui.run("verify", // QUIET,
				filename("predicate-bad_decl_twice.cvl")));
	}

}
