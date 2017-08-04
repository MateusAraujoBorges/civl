package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.IOException;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * OMP transformer testing on LLNL polybench(part of dataracebench). TODO: Need
 * to change <polybench.h> to "utilities/polybench.h" in c source. any better
 * ways?
 * 
 * @author dxu
 */

public class OmpPolybenchTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(
			new File("examples/omp/dataracebench-1.0.0"), "micro-benchmarks");

	private static UserInterface ui = new UserInterface();

	// private static List<String> codes = Arrays.asList("prune", "sef");

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	private void check(String filenameRoot, boolean debug)
			throws ABCException, IOException {
		ui.run("verify", "-input_omp_thread_max=2", "-DPOLYBENCH_TIME ",
				filename(filenameRoot + ".c"),
				"examples/omp/dataracebench-1.0.0/micro-benchmarks/utilities/polybench.c");

		// assertTrue(ui.run("show", "-showModel", "-ompNoSimplify",
		// filename(filenameRoot+".c")));

	}

	/* **************************** Test Methods *************************** */

	@Test(timeout = 600000)
	public void mmparallelno() throws ABCException, IOException {
		check("3mm-parallel-no", false);
	}

	@Test(timeout = 600000)
	public void mmtileno() throws ABCException, IOException {
		check("3mm-tile-no", false);
	}

	@Test(timeout = 600000)
	public void adiparallelno() throws ABCException, IOException {
		check("adi-parallel-no", false);
	}

	@Test(timeout = 600000)
	public void aditileno() throws ABCException, IOException {
		check("adi-tile-no", false);
	}

	@Test(timeout = 600000)
	public void jacobi2dparallelno() throws ABCException, IOException {
		check("jacobi2d-parallel-no", false);
	}

	@Test(timeout = 600000)
	public void jacobi2dtileno() throws ABCException, IOException {
		check("jacobi2d-tile-no", false);
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
