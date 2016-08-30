package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class DirectedTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "direct");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	/* **************************** Test Methods *************************** */

	@Test
	public void itestShow() throws ABCException {
		assertTrue(ui.run("show", "-showProgram", "-direct="+filename("itest.direct"), filename("itest.c") ));
	}
	
	@Test
	public void itestVerify() throws ABCException {
		assertTrue(ui.run("verify", "-showProgram", "-direct="+filename("itest.direct"), filename("itest.c") ));
	}
	
	@Test
	public void infeasibleShow() throws ABCException {
		assertTrue(ui.run("show", "-showProgram", "-direct="+filename("infeasible.direct"), filename("infeasible.c") ));
	}
	
	@Test
	public void infeasibleVerify() throws ABCException {
		assertTrue(ui.run("verify", "-showProgram", "-direct="+filename("infeasible.direct"), filename("infeasible.c") ));
	}
	
	@Test
	public void full() throws ABCException {
		assertTrue(ui.run("verify", "-showProgram", filename("fullvsdirect.c")));
	}
	
	@Test
	public void direct() throws ABCException {
		assertTrue(ui.run("verify", "-showProgram", "-direct="+filename("fullvsdirect.direct"), filename("fullvsdirect.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
