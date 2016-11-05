package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;

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
	 * the given C file equals the oracle slice file (where equivalence is defined
	 * as the Set<String> of lines being the same), which is stored as a file with
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
		Set<String> newSliceSet = createFileLineSet(newSliceFileStr);
		
		String oracleSliceFileStr = "examples/slice/"+filenameRoot+"_0.trace.slice";
		Set<String> oracleSliceSet = createFileLineSet(oracleSliceFileStr);
		
		return newSliceSet.equals(oracleSliceSet);
	}
	
	public Set<String> createFileLineSet(String fileName) {
		
		Set<String> lineSet = new HashSet<>();
		
		try {
			File file = new File(fileName);
			Scanner scanner = new Scanner(file);
			while (scanner.hasNext()) {
				lineSet.add(scanner.next());
			}
			scanner.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} 
		
		return lineSet;
		  
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
	
	@Test
	public void intraproceduralTest() throws ABCException, FileNotFoundException {	
		assertTrue(check("intraprocedural"));
	}
	
	@Test
	public void interproceduralOneDependencyTest() throws ABCException, FileNotFoundException {	
		assertTrue(check("interprocedural_one_dependency"));
	}
	
	@Test
	public void interproceduralTwoDependenciesTest() throws ABCException, FileNotFoundException {	
		assertTrue(check("interprocedural_two_dependencies"));
	}
	
	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
