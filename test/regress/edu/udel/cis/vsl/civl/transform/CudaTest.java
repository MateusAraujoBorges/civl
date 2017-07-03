package edu.udel.cis.vsl.civl.transform;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.TestConstants;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class CudaTest {

	/* *************************** Static Fields *************************** */

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "cuda");

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* *************************** Test Methods **************************** */

	@Test
	public void sum() {
		assertTrue(
				ui.run("verify -enablePrintf=false -intOperationTransformer=true -inputN=8 -inputNBLOCKS=4",
						TestConstants.QUIET, filename("sum.cu")));
	}

	@Test
	public void matMult1() {
		assertTrue(
				ui.run("verify -enablePrintf=false -intOperationTransformer=true -inputN=2 -inputTILE_WIDTH=1 ",
						TestConstants.QUIET, filename("matMult1.cu")));
	}

	@Test
	public void dotTest() {
		assertTrue(
				ui.run("verify -intOperationTransformer=true -inputN_B=3 -input threadsPerBlock_B=3",
						TestConstants.QUIET, filename("dot.cu")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
