package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LibraryTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "library");

	private static UserInterface ui = new UserInterface();

	private final static String CIVLC = "civlc";

	// private final static String OMP = "omp";

	private final static String STDIO = "stdio";

	private final static String STDLIB = "stdlib";
	private final static String STRING = "string";
	private final static String TIME = "time";
	private final static String POINTER = "pointer";
	private final static String IncompatPtrTranslationDir = POINTER
			+ "/incompatiblePointerTranslation_dir";
	@SuppressWarnings("unused")
	private final static String EXTERNAL = "external";
	private final static String MATH = "math";
	private final static String COLLATE = "collate";

	/* *************************** Helper Methods *************************** */

	private static String filename(String subfolder, String name) {
		return new File(new File(rootDir, subfolder), name).getPath();
	}

	private static String filename(String name) {
		return filename(".", name);
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void assertBad() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "assertBad.cvl")));
	}

	@Test
	public void elaborate() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(CIVLC, "elaborate.cvl")));
	}

	@Test
	public void elaborate1() throws ABCException {
		assertTrue(ui.run("verify -enablePrintf=false", QUIET,
				filename(CIVLC, "elaborate1.cvl")));
	}

	@Test
	public void string() throws ABCException {
		assertTrue(
				ui.run("verify", QUIET, filename(STRING, "string_test.cvl")));
	}

	@Test
	public void memset() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(STRING, "memset.cvl")));
	}

	@Test
	public void memcpy_multi_dim_one() throws ABCException {
		assertTrue(ui.run("verify", QUIET,
				filename(STRING, "memcpy_multi_dim_one.c")));
	}

	@Test
	public void assertH() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename("assert_test.cvl")));
	}

	@Test
	public void printf() throws ABCException {
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(STDIO, "printf.cvl")));
	}

	@Test
	public void fprintf() throws ABCException {
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(STDIO, "fprintf.cvl")));
	}

	@Test
	public void printfBad() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(STDIO, "printfBad.cvl")));
	}

	@Test
	public void communicatorFeatures() {
		assertTrue(ui.run("verify", "-inputNPROCS=2", "-inputN_BOUND=2",
				NO_PRINTF, QUIET, filename(CIVLC, "communicatorFeatures.cvl")));
	}

	@Test
	public void commBad() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "commBad.cvl")));
	}

	@Test
	public void commTest() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "commTest.cvl")));
	}

	@Test
	public void malloc1() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(STDLIB, "malloc.cvl")));
	}

	@Test
	public void malloc2() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(STDLIB, "malloc2.c")));
	}

	@Test
	public void malloc3() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(STDLIB, "malloc3.c")));
	}

	@Test
	public void mallocForSturct() throws ABCException {
		assertTrue(ui.run("verify", QUIET,
				filename(STDLIB, "mallocForStruct.cvl")));

	}

	@Test
	public void calloc1() {
		assertTrue(ui.run(VERIFY, QUIET, filename(STDLIB, "calloc1.cvl")));
	}

	@Test
	public void calloc2() {
		assertTrue(ui.run(VERIFY, QUIET, filename(STDLIB, "calloc2.cvl")));
	}

	@Test
	public void calloc3_unimplementedFeature() {
		assertFalse(ui.run(VERIFY, QUIET, filename(STDLIB, "calloc3.cvl")));
	}

	@Test
	public void memcpy() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(STRING, "memcpy.cvl")));
	}

	@Test
	public void strlen_concrete() throws ABCException {
		assertTrue(
				ui.run("verify", QUIET, filename(STRING, "strlen_concrete.c")));
	}

	@Test
	public void strlen_symbolic() throws ABCException {
		assertTrue(
				ui.run("verify", QUIET, filename(STRING, "strlen_symbolic.c")));
	}

	@Test
	public void messageUnpackBad1() throws ABCException {
		assertFalse(ui.run("verify", QUIET, NO_PRINTF,
				filename(CIVLC, "messageUnpackBad1.cvl")));
	}

	@Test
	public void messageUnpackBad2() throws ABCException {
		assertFalse(ui.run("verify", QUIET,
				filename(CIVLC, "messageUnpackBad2.cvl")));
	}

	@Test
	public void barrier() throws ABCException {
		assertTrue(ui.run("verify", "-inputN=2", QUIET,
				filename(CIVLC, "barrier.cvl")));
	}

	@Test
	public void chooseInt() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "chooseInt.cvl")));
	}

	@Test
	public void exit() {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "exit.cvl")));
	}

	@Test
	public void exitBad() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "exitBad.cvl")));
	}

	@Test
	public void h() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "contains.cvl")));
	}

	@Test
	public void equals() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "equals.cvl")));
	}

	@Test
	public void translatePointer() throws ABCException {
		assertTrue(
				ui.run("verify", QUIET, filename(CIVLC, "translate_ptr.cvl")));
	}

	@Test
	public void copy() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "copy.cvl")));
	}

	@Test
	public void seq() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "seqTest.cvl")));
	}

	@Test
	public void freeBad1() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "freeBad1.cvl")));
	}

	@Test
	public void freeBad2() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "freeBad2.cvl")));
	}

	@Test
	public void bundleAndHeap() throws ABCException {
		assertTrue(
				ui.run("verify", QUIET, filename(CIVLC, "bundleAndHeap.cvl")));
	}

	@Test
	public void random() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(STDLIB, "random.cvl")));
	}

	@Test
	public void rand_r() throws ABCException {
		assertTrue(
				ui.run("verify -D_LINUX", QUIET, filename(STDLIB, "rand_r.c")));
	}

	@Test
	public void domainDecomp() throws ABCException {
		assertTrue(ui.run("verify", "-inputn=4", NO_PRINTF, QUIET,
				filename(CIVLC, "domainDecomposition.cvl")));
	}

	@Test
	public void timeTest() throws ABCException {
		assertTrue(ui.run("verify", "-inputN=10", NO_PRINTF, QUIET,
				filename(TIME, "timeTest.cvl")));
	}

	@Test
	public void localTime() throws ABCException {
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(TIME, "localTime.c")));
	}

	@Test
	public void assertEquals() throws ABCException {
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(POINTER, "simpleAssertEquals.cvl")));
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(POINTER, "simpleAssertEquals2.cvl")));
	}

	@Test
	public void assertEqualsFail() throws ABCException {
		assertFalse(ui.run("verify", NO_PRINTF, QUIET,
				filename(POINTER, "simpleAssertEqualsFail.cvl")));
		assertFalse(ui.run("verify", NO_PRINTF, QUIET,
				filename(POINTER, "simpleAssertEqualsFail2.cvl")));
	}

	@Test
	public void assume() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "assume.cvl")));
	}

	@Test
	public void assume1() throws ABCException {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "assume1.cvl")));
	}

	@Test
	public void fprintfExit() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(STDIO, "fprintfExit.cvl")));
	}

	@Test
	public void scanfExit() throws ABCException {
		assertTrue(ui.run("verify -verbose=false", QUIET,
				filename(STDIO, "scanfExit.cvl")));
	}

	@Test
	public void systemFunctionPointer() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename("funcPointer.cvl")));
	}

	@Test
	public void pathcondition() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(CIVLC, "pathcondition.cvl")));
	}

	@Test
	public void isConcreteInt() throws ABCException {
		assertTrue(ui.run("verify", QUIET,
				filename(CIVLC, "concreteIntTest.cvl")));
	}

	@Test
	public void elaborateDomain() throws ABCException {
		assertTrue(ui.run("verify", NO_PRINTF, QUIET,
				filename(CIVLC, "elaborateDomain.cvl")));
	}

	@Test
	public void sqrt() throws ABCException {
		assertTrue(
				ui.run("verify ", QUIET, NO_PRINTF, filename(MATH, "sqrt.c")));
	}

	@Test
	public void floor() throws ABCException {
		assertTrue(
				ui.run("verify ", QUIET, NO_PRINTF, filename(MATH, "floor.c")));
	}

	@Test
	public void ceil() throws ABCException {
		assertTrue(
				ui.run("verify ", QUIET, NO_PRINTF, filename(MATH, "ceil.c")));
	}

	@Test
	public void floorCeilCast() throws ABCException {
		assertTrue(ui.run("verify ", QUIET, NO_PRINTF,
				filename(MATH, "floor_ceil_cast.c")));
	}

	@Test
	public void exitTest() throws ABCException {
		assertTrue(ui.run("verify", QUIET, filename(STDLIB, "exitTest.c")));
	}

	@Test
	public void havoc() throws ABCException {
		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(CIVLC, "havoc.cvl")));

		assertTrue(ui.run("verify", QUIET, NO_PRINTF,
				filename(CIVLC, "simpleHavocTest.cvl")));
	}

	@Test
	public void havocBad() throws ABCException {
		assertFalse(ui.run("verify", NO_PRINTF, QUIET,
				filename(CIVLC, "havocBad.cvl")));
	}

	@Test
	public void heap() {
		assertFalse(ui.run("verify", QUIET, filename(CIVLC, "heap.cvl")));
	}

	@Test
	public void power() {
		assertTrue(ui.run("verify", QUIET, filename(CIVLC, "pow.cvl")));
	}

	@Test
	public void completeCollateState() {
		assertTrue(ui.run("verify", QUIET,
				filename(COLLATE, "completeCollateState.cvl")));
	}

	@Test
	public void simpleCopyTest() {
		assertTrue(ui.run("verify", QUIET,
				filename(POINTER, "simpleCopyTest.cvl")));
	}

	@Test
	public void undefinedVarTest() {
		assertFalse(
				ui.run("verify", QUIET, filename(POINTER, "undefinedVar.cvl")));
	}

	@Test
	public void incomptPointerTranslationStructTest() {
		assertFalse(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationStruct.cvl")));
	}

	@Test
	public void incomptPointerTranslationStructFixTest() {
		assertTrue(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationStructFix.cvl")));
	}

	@Test
	public void incomptPointerTranslationUnionTest() {
		assertFalse(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationUnion.cvl")));
	}

	@Test
	public void incomptPointerTranslationUnionFixTest() {
		assertTrue(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationUnionFix.cvl")));
	}

	@Test
	public void incomptPointerTranslationComplexTest() {
		assertFalse(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationComplex.cvl")));
	}

	@Test
	public void incomptPointerTranslationComplex2Test() {
		assertFalse(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationComplex2.cvl")));
	}

	@Test
	public void incomptPointerTranslationComplex3Test() {
		assertFalse(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationComplex3.cvl")));
	}

	@Test
	public void incomptPointerTranslationComplexFixTest() {
		assertTrue(ui.run("verify", QUIET, filename(IncompatPtrTranslationDir,
				"incompatiblePointerTranslationComplexFix.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
