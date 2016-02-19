package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class LanguageFeaturesTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"languageFeatures");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods *************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void abstractFun() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("abstractFun.cvl")));
	}

	@Test
	public void abstractFunNoArg() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("abstractFunNoArg.cvl")));
	}

	@Test
	public void arrayLiteral() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				"-enablePrintf=false", filename("arrayLiteral.cvl")));
	}

	@Test
	public void arrayPointer() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("arrayPointer.cvl")));
	}

	@Test
	public void arrays() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("arrays.cvl")));
	}

	@Test
	public void assertNonNullPointer() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("assertNonNullPointer.cvl")));
	}

	@Test
	public void assertNullPointer() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("assertNullPointer.cvl")));
	}

	@Test
	public void assertPrintf() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("assertPrintf.cvl")));
	}

	@Test
	public void assume() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("assume.cvl")));
	}

	@Test
	public void atomChooseBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("atomChooseBad.cvl")));
	}

	@Test
	public void atomicBlockedResume() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("atomicBlockedResume.cvl")));
	}

	@Test
	public void atomicStatement() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("atomicStatement.cvl")));
	}

	@Test
	public void atomicWait() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputN=3", 
				TestConstants.QUIET, filename("atomicWait.cvl")));
	}

	@Test
	public void atomStatement() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("atomStatement.cvl")));
	}

	@Test
	public void atomWaitBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("atomWaitBad.cvl")));
	}

	@Test
	public void badGuard() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("badGuard.cvl")));
	}

	/**
	 * This should be moved to test/dev.
	 */
	@Ignore
	@Test
	public void bigO() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("bigO.cvl")));
	}

	@Test
	public void bitwise() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("bitwise.cvl")));
	}

	@Test
	public void breakStatement() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("break.cvl")));
	}

	@Test
	public void bundleArray() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("bundleArray.cvl")));
	}

	@Test
	public void bundleTest() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("bundleTest.cvl")));
	}

	@Test
	public void bundleTestBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("bundleTestBad.cvl")));
	}

	@Test
	public void bundleConcrete() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("bundleConcrete.cvl")));
	}

	@Test
	public void bundleSize() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("bundleSize.cvl")));
	}

	@Test
	public void bundleStruct() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("bundleStruct.cvl")));
	}

	@Test
	public void cast() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("cast.cvl")));
	}

	@Test
	public void charTest() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("char.cvl")));
	}

	@Test
	public void choose() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("choose.cvl")));
	}

	@Test
	public void choose_int() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("choose_int.cvl")));
	}

	@Test
	public void compare() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("compare.cvl")));
	}

	@Test
	public void conditionalExpression() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("conditionalExpression.cvl")));
	}

	@Test
	public void continueStatement() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("continue.cvl")));
	}

	@Test
	public void duffs() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("duffs.cvl")));
	}

	@Test
	public void dynamicStruct() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("dynamicStruct.cvl")));
	}

	@Test
	public void divisionByZero() throws ABCException {
		
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				TestConstants.errorBound(2), filename("divisionByZero.cvl")));
	}

	@Test
	public void divisionByZero_Ignore() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_CHECK_DIVISION_BY_ZERO,
				TestConstants.QUIET, filename("divisionByZero.cvl")));
	}

	@Test
	public void emptyWhen() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("emptyWhen.cvl")));
	}

	@Test
	public void forLoop() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("for.cvl")));
	}

	@Test
	public void functionPrototype() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("functionPrototype.cvl")));
	}

	@Test
	public void functionPrototypeBad() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("functionPrototypeBad.cvl")));
	}

	@Test
	public void implies() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("implies.cvl")));
	}

	@Test
	public void linkedList() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("linkedList.cvl")));
	}

	@Test
	public void malloc() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("malloc.cvl")));
	}

	@Test
	public void notValidResultType() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(2),
				TestConstants.QUIET, filename("notValidResultType.cvl")));
	}

	@Test
	public void mallocBad() throws ABCException {
		assertFalse(ui
				.run(TestConstants.VERIFY, TestConstants.errorBound(3),
						TestConstants.QUIET, filename("mallocBad.cvl")));
	}

	@Test
	public void mallocBad2() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("mallocBad2.cvl")));
	}

	@Test
	public void minimal() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("minimal.cvl")));
	}

	@Test
	public void nonbooleanCondition() throws IOException,
			PreprocessorException, ParseException, SyntaxException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("nonbooleanCondition.cvl")));
	}

	@Test
	public void nullPointer() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("null.cvl")));
	}

	@Test
	public void pointers() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointers.cvl")));
	}

	@Test
	public void pointersBad() throws ABCException {
		assertFalse(ui
				.run("verify -errorBound=10", filename("pointersBad.cvl")));
		assertFalse(ui.run("verify -DICLeafNode", filename("pointersBad.cvl")));
		assertFalse(ui.run("verify -DNCLeafNode", filename("pointersBad.cvl")));
		assertFalse(ui.run("verify -DUNION", filename("pointersBad.cvl")));
	}

	@Test
	public void pointerAdd() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAdd.cvl")));
	}

	@Test
	public void pointerAdd2() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAdd2.cvl")));
	}

	@Test
	public void pointerAddBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad.cvl")));
	}

	@Test
	public void pointerAddBad2() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad2.cvl")));
	}

	@Test
	public void pointerAddBad3() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad3.c")));
	}

	@Test
	public void pointerAddBad4() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad4.c")));
	}

	@Test
	public void pointerAddBad5() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad5.c")));
	}

	@Test
	public void pointerAddBad6() throws ABCException {
		assertFalse(ui
				.run(TestConstants.VERIFY, TestConstants.errorBound(2),
						TestConstants.QUIET, filename("pointerAddBad6.c")));
	}

	@Test
	public void pointerAdd6() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAdd6.c")));
	}

	@Test
	public void pointerAddBad7() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAddBad7.c")));
	}

	@Test
	public void quantifiers() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("quantifiers.cvl")));
	}

	@Test
	public void removedHeapPointer() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("removedHeapPointer.cvl")));
	}

	@Test
	public void scopeOperators() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
				TestConstants.QUIET, filename("scopeOperators.cvl")));
	}

	@Test
	public void scoping() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("scoping.cvl")));
	}

	@Test
	public void self() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("self.cvl")));
	}

	@Test
	public void sideEffects() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("sideEffects.cvl")));
	}

	@Test
	public void sizeOf() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("sizeof.cvl")));
	}

	@Test
	public void spawnFoo() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("spawnFoo.cvl")));
	}

	@Test
	public void struct() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("struct.cvl")));
	}

	@Test
	public void structArray() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("structArray.cvl")));
	}

	@Test
	public void structStruct() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("structStruct.cvl")));
	}

	@Test
	public void switchBlock() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("switch.cvl")));
	}

	@Test
	public void union() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("union.cvl")));
	}

	@Test
	public void enum1() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("enum1.cvl")));
	}

	@Test
	public void enum2() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("enum2.cvl")));
	}

	@Test
	public void functionPointer() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
				TestConstants.QUIET, filename("functionPointer.cvl")));
	}

	@Test
	public void undefPointer() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("undefPointer.cvl")));
	}

	@Test
	public void undefHeapPointer() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("undefHeapPointer.cvl")));
	}

	@Test
	public void sideEffectLoop() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("sideEffectLoop.cvl")));
	}

	@Test
	public void assignInput() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("assignInput.cvl")));
	}

	@Test
	public void inputBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("inputBad.cvl")));
	}

	@Test
	public void outputBad() throws ABCException {
		assertFalse(ui.run("verify -errorBound=5", TestConstants.QUIET,
				filename("outputBad.cvl")));
	}

	@Test
	public void procNull() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("procNull.cvl")));
	}

	@Test
	public void functionBad() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("functionBad.cvl")));
	}

	@Test
	public void intToBool() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("intToBool.cvl")));
	}

	@Test
	public void twoDpointerTest() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("2dpointerTest.cvl")));
	}

	@Test
	public void memoryLeak() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("memoryLeak.cvl")));
	}

	@Test
	public void processLeak() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(2),
				TestConstants.QUIET, filename("processLeak.cvl")));
	}

	@Test
	public void comma() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputn=5", 
				TestConstants.QUIET, filename("comma.cvl")));
	}

	@Test
	public void assignIntWtReal() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("assignIntWtReal.cvl")));
	}

	@Test
	public void civlPragma() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputNB=5", 
				TestConstants.QUIET, filename("civlPragma.cvl")));
	}

	@Test
	public void civlFor() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
				TestConstants.QUIET, filename("civlfor.cvl")));
	}

	@Test
	public void civlParfor() throws ABCException {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
				TestConstants.QUIET, filename("civlParfor.cvl")));
	}

	@Test
	public void civlParforNotConcrete() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(2),
				TestConstants.NO_PRINTF, TestConstants.QUIET, 
				filename("civlParforNotConcrete.cvl")));
	}

	@Test
	public void pointerSub() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("pointerSubtraction.cvl")));
	}

	@Test
	public void pointerSubBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("pointerSubtractionBad.cvl")));
	}

	@Test
	public void pointerSubBad2() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("pointerSubtractionBad2.cvl")));
	}

	@Test
	public void stringTest() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("stringTest.cvl")));
	}

	@Test
	public void int2char() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("int2char.cvl")));
	}

	@Test
	public void int2charBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("int2charBad.cvl")));
	}

	@Test
	public void int2charBad2() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("int2charBad2.cvl")));
	}

	@Test
	public void include1() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-userIncludePath=" + rootDir.getPath(),
				filename("include1.cvl")));
	}

	@Test
	public void procBound() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.procBound(10), 
				TestConstants.NO_SHOW_TRANSITIONS, TestConstants.NO_SHOW_SAVED_STATES,
				TestConstants.QUIET, filename("procBound.cvl")));
	}

	@Test
	public void not() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("not.cvl")));
	}

	@Test
	public void noopBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("noopBad.cvl")));
	}

	@Test
	public void pointerAdd1() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("pointerAdd1.cvl")));
		assertFalse(ui.run(TestConstants.VERIFY, "-DWRONG", TestConstants.QUIET,
				filename("pointerAdd1.cvl")));
		assertTrue(ui.run(TestConstants.VERIFY, "-DARRAY", TestConstants.QUIET,
				filename("pointerAdd1.cvl")));
		assertFalse(ui.run(TestConstants.VERIFY, "-DARRAY -DWRONG", TestConstants.QUIET,
				filename("pointerAdd1.cvl")));
	}

	@Test
	public void int2float() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("int2float.cvl")));
	}

	@Test
	public void initVal() throws ABCException {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("initialValues.cvl")));
	}

	@Test
	public void valueUndefinedTest() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(10),
				TestConstants.QUIET, filename("civlValueUndefined.cvl")));
	}

	@Test
	public void staticVar() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("staticVar.cvl")));
	}

	@Test
	public void libraryException() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.errorBound(3),
				"-userIncludePath=examples/library/foo", TestConstants.QUIET,
				filename("libraryException.cvl")));
	}

	@Test
	public void conditionalLHS() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("condLHS.c")));
	}

	@Test
	public void intToPointer() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("intToPointer.cvl")));
	}

	@Test
	public void splitFormat() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("splitFormat.cvl")));
	}

	@Test
	public void splitFormatBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("splitFormatBad.cvl")));
	}

	@Test
	public void splitFormatBad2() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("splitFormatBad2.cvl")));
	}

	@Test
	public void splitFormatBad3() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("splitFormatBad3.cvl")));
	}

	// quantifiedComp.cvl
	@Test
	public void quantifiedComp() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("quantifiedComp.cvl")));
	}

	@Test
	public void atomicFunctionSpecifier() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("atomicFunctionSpecifier.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
