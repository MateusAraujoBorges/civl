package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class SliceTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "slice");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}
	
	/*
	 * check whether the file produced by running 'civl replay -sliceAnalysis' on
	 * the given C file equals the oracle slice file, which is stored as a file with
	 * an added suffix of ".slice" in the subdirectory "examples/slice".
	 * 
	 * @param filenameRoot The file name of the C program (without
	 * extension).
	 * 
	 * @throws ABCException
	 * 
	 * @throws FileNotFoundException
	 */
	private boolean check(String filenameRoot) throws ABCException, FileNotFoundException {
		String fileStr = filenameRoot + ".c";
		
		ui.run("verify", "-svcomp16", filename(fileStr));
		ui.run("replay", "-sliceAnalysis", filename(fileStr));
		
		String newSliceFileStr = "CIVLREP/"+filenameRoot+"_0.trace.slice";
		File newSliceFile = new File(newSliceFileStr);
		Scanner testScanner = new Scanner(newSliceFile);
		String newSliceStr = testScanner.useDelimiter("\\Z").next();
		testScanner.close();
		
		String oracleSliceFileStr = "examples/slice/"+filenameRoot+"_0.trace.slice";
		File oracleSliceFile = new File(oracleSliceFileStr);
		Scanner oracleScanner = new Scanner(oracleSliceFile);
		String oracleSliceStr = oracleScanner.useDelimiter("\\Z").next();
		oracleScanner.close();
		
		return newSliceStr.equals(oracleSliceStr);
	}
	/* **************************** Test Methods *************************** */

	@Test
	public void simpleTest() throws ABCException, FileNotFoundException {	
		assertTrue(check("simple"));
	}
	
	@Test
	public void subsumptionTest() throws ABCException, FileNotFoundException {	
		assertTrue(check("subsumption"));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
