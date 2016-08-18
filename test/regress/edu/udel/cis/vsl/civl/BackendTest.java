package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static edu.udel.cis.vsl.civl.TestConstants.errorBound;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class BackendTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "backend");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void printExpr() {
		assertTrue(ui.run(VERIFY, QUIET, filename("printExpr.cvl")));
	}

	@Test
	public void arrayWrite() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayWrite.cvl")));
	}

	@Test
	public void showTrans() {
		assertTrue(ui.run(VERIFY, QUIET, filename("showTrans.cvl")));
	}

	@Test
	public void sizeOfTypes() {
		assertTrue(ui.run(VERIFY, QUIET, filename("sizeOfTypes.c")));
	}

	@Test
	public void symbolicConsts() {
		assertFalse(ui.run(VERIFY, QUIET, filename("symbolicConstants.cvl")));
	}

	@Test
	public void returnNull() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2), NO_PRINTF, QUIET,
				filename("returnNull.cvl")));
	}

	@Test
	public void quantified() {
		assertTrue(ui.run(VERIFY, QUIET, filename("quantified.cvl")));
	}

	@Test
	public void mpiSumArray() {
		assertTrue(ui.run("show -showInputs", "-input_mpi_nprocs=3",
				filename("mpiSumarray.cvl")));
	}

	@Test
	public void symbols() {
		assertTrue(ui.run(VERIFY, QUIET, filename("symbols.cvl")));
	}

	@Test
	public void binaryGuard() {
		assertTrue(ui.run(VERIFY, QUIET, filename("binaryGuard.cvl")));
	}

	@Test
	public void atomicBlocking() {
		assertFalse(ui.run(VERIFY, QUIET, filename("atomicExample.c")));
	}

	@Test
	public void atomicBlocking2() {
		assertFalse(ui.run(VERIFY, QUIET, filename("atomic2.c")));
	}

	@Test
	public void valueAt() {
		assertTrue(ui.run(VERIFY, "-showTransitions", filename("valueat.cvl")));
	}

	@Test
	public void valueAt_seq() {
		assertTrue(ui.run(VERIFY, QUIET, filename("valueat_seq.cvl")));
	}

	@Test
	public void arrayLambda() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayLambda.cvl")));
	}

	@Test
	public void sizeof() {
		ui.run(VERIFY, QUIET, filename("sizeof.cvl"));
	}

	@Test
	public void original() {
		ui.run(VERIFY, QUIET, filename("original.cvl"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
