package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.NO_PRINTF;
import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static edu.udel.cis.vsl.civl.TestConstants.errorBound;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
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
		assertTrue(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("abstractFun.cvl")));
	}

	@Test
	public void abstractFunNoArg() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("abstractFunNoArg.cvl")));
	}

	@Test
	public void arbitraryPointer() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arbitrary_pointer.cvl")));
	}

	@Test
	public void arbitraryPointerBad() {
		assertFalse(
				ui.run(VERIFY, QUIET, filename("arbitrary_pointer_bad.cvl")));
	}

	@Test
	public void arrayLiteral() throws ABCException {
		assertTrue(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("arrayLiteral.cvl")));
	}

	@Test
	public void arrayPointer() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayPointer.cvl")));
	}

	@Test
	public void arrays() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrays.cvl")));
	}

	@Test
	public void arrayDefProblem() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("arrayDefProblem.cvl")));
	}

	@Test
	public void arrayOfStructs() throws ABCException {
		assertTrue(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("arrayOfStruct.c")));
	}

	@Test
	public void assertNonNullPointer() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("assertNonNullPointer.cvl")));
	}

	@Test
	public void assertNullPointer() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("assertNullPointer.cvl")));
	}

	@Test
	public void assertPrintf() throws ABCException {
		assertFalse(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("assertPrintf.cvl")));
	}

	@Test
	public void assume() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("assume.cvl")));
	}

	@Test
	public void atomChooseBad() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("atomChooseBad.cvl")));
	}

	@Test
	public void atomicBlockedResume() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("atomicBlockedResume.cvl")));
	}

	@Test
	public void atomicStatement() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("atomicStatement.cvl")));
	}

	@Test
	public void arrayDeclExtent() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("arrayDeclExtent.c")));
	}

	@Test
	public void atomicWait() throws ABCException {
		assertTrue(
				ui.run(VERIFY, "-inputN=3", QUIET, filename("atomicWait.cvl")));
	}

	@Test
	public void atomStatement() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("atomStatement.cvl")));
	}

	@Test
	public void atomWaitBad() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("atomWaitBad.cvl")));
	}

	@Test
	public void badGuard() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("badGuard.cvl")));
	}

	@Test
	public void bitwise() {
		assertTrue(ui.run(VERIFY, QUIET, filename("bitwise.cvl")));
	}

	@Test
	public void breakStatement() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("break.cvl")));
	}

	@Test
	public void bundleArray() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleArray.cvl")));
	}

	@Test
	public void bundleTest() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleTest.cvl")));
	}

	@Test
	public void bundleTestBad() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("bundleTestBad.cvl")));
	}

	@Test
	public void bundleConcrete() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleConcrete.cvl")));
	}

	@Test
	public void bundleSize() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleSize.cvl")));
	}

	@Test
	public void bundleStruct() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleStruct.cvl")));
	}

	@Test
	public void bundleUnpackApply() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("bundleUnpackApply.cvl")));
	}

	@Test
	public void cast() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("cast.cvl")));
	}

	@Test
	public void castReal2Int() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("castReal2Int.cvl")));
	}

	@Test
	public void charTest() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("char.cvl")));
	}

	@Test
	public void choose() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("choose.cvl")));
	}

	@Test
	public void choose_int() throws ABCException {
		assertTrue(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("choose_int.cvl")));
	}

	@Test
	public void compare() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("compare.cvl")));
	}

	@Test
	public void conditionalExpression() throws ABCException {
		assertTrue(
				ui.run(VERIFY, QUIET, filename("conditionalExpression.cvl")));
	}

	@Test
	public void continueStatement() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("continue.cvl")));
	}

	@Test
	public void duffs() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("duffs.cvl")));
	}

	@Test
	public void dynamicStruct() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("dynamicStruct.cvl")));
	}

	@Test
	public void divisionByZero() throws ABCException {

		assertFalse(ui.run(VERIFY, QUIET, errorBound(2),
				"-intOperationTransformer=true",
				filename("divisionByZero.cvl")));
	}

	@Test
	public void divisionByZero_Ignore() throws ABCException {
		assertTrue(ui.run(VERIFY, "-checkDivisionByZero=false", QUIET,
				filename("divisionByZero.cvl")));
	}

	@Test
	public void divisionByZeroConstant() throws ABCException {

		assertFalse(ui.run(VERIFY, QUIET, errorBound(2),
				"-intOperationTransformer=true",
				filename("divisionByZeroConstant.cvl")));
	}

	@Test
	public void divisionByZeroConstant_Ignore() throws ABCException {
		assertTrue(ui.run(VERIFY, "-checkDivisionByZero=false", QUIET,
				filename("divisionByZeroConstant.cvl")));
	}

	@Test
	public void emptyWhen() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("emptyWhen.cvl")));
	}

	@Test
	public void forLoop() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("for.cvl")));
	}

	@Test
	public void functionPrototype() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("functionPrototype.cvl")));
	}

	@Test
	public void functionPrototypeBad() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("functionPrototypeBad.cvl")));
	}

	@Test
	public void funcRetStruct() {
		assertTrue(ui.run("verify", TestConstants.QUIET,
				filename("functionRetStruct.cvl")));
	}

	@Test
	public void implies() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("implies.cvl")));
	}

	@Test
	public void linkedList() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("linkedList.cvl")));
	}

	@Test
	public void malloc() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("malloc.cvl")));
	}

	@Test
	public void notValidResultType() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2), QUIET,
				filename("notValidResultType.cvl")));
	}

	@Test
	public void mallocBad() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(3), QUIET,
				filename("mallocBad.cvl")));
	}

	@Test
	public void mallocBad2() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("mallocBad2.cvl")));
	}

	@Test
	public void minimal() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("minimal.cvl")));
	}

	@Test
	public void nonbooleanCondition() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		assertTrue(ui.run(VERIFY, QUIET, filename("nonbooleanCondition.cvl")));
	}

	@Test
	public void nullPointer() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("null.cvl")));
	}

	@Test
	public void pointers() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("pointers.cvl")));
	}

	@Test
	public void pointersBad() throws ABCException {
		// TODO: separate into different tests
		assertFalse(ui.run("verify -errorBound=10", QUIET,
				filename("pointersBad.cvl")));
		assertFalse(ui.run("verify -DICLeafNode", QUIET,
				filename("pointersBad.cvl")));
		assertFalse(ui.run("verify -DNCLeafNode", QUIET,
				filename("pointersBad.cvl")));
		assertFalse(
				ui.run("verify -DUNION", QUIET, filename("pointersBad.cvl")));
	}

	@Test
	public void pointerAdd() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("pointerAdd.cvl")));
	}

	@Test
	public void pointerAdd2() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("pointerAdd2.cvl")));
	}

	@Test
	public void pointerAddBad() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad.cvl")));
	}

	@Test
	public void pointerAddBad2() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad2.cvl")));
	}

	@Test
	public void pointerAddBad3() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad3.c")));
	}

	@Test
	public void pointerAddBad4() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad4.c")));
	}

	@Test
	public void pointerAddBad5() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad5.c")));
	}

	@Test
	public void pointerAddBad6() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2), QUIET,
				filename("pointerAddBad6.c")));
	}

	@Test
	public void pointerAdd6() {
		assertTrue(ui.run(VERIFY, QUIET, filename("pointerAdd6.c")));
	}

	@Test
	public void pointerAddBad7() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("pointerAddBad7.c")));
	}

	@Test
	public void quantifiers() {
		assertTrue(ui.run(VERIFY, QUIET, filename("quantifiers.cvl")));
	}

	@Test
	public void quantifiers2() {
		assertTrue(ui.run(VERIFY, QUIET, filename("quantifiers2.cvl")));
	}

	@Test
	public void removedHeapPointer() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("removedHeapPointer.cvl")));
	}

	@Test
	public void runBad() {
		assertFalse(ui.run(VERIFY, QUIET, filename("runStatementBad.cvl")));
	}

	@Test
	public void runGood() {
		assertTrue(ui.run(VERIFY, QUIET, filename("runStatement.cvl")));
	}

	@Test
	public void stateNullObjects() {
		assertTrue(ui.run(VERIFY, QUIET, filename("stateNull.cvl")));
	}

	@Test
	public void runDining() {
		assertTrue(ui.run(VERIFY, QUIET, filename("runDining.cvl")));
	}

	@Test
	public void scopeOperators() throws ABCException {
		assertTrue(ui.run(VERIFY, NO_PRINTF, QUIET,
				filename("scopeOperators.cvl")));
	}

	@Test
	public void scoping() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("scoping.cvl")));
	}

	@Test
	public void self() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("self.cvl")));
	}

	@Test
	public void sideEffects() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("sideEffects.cvl")));
	}

	@Test
	public void sizeOf() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("sizeof.cvl")));
	}

	@Test
	public void spawnFoo() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("spawnFoo.cvl")));
	}

	@Test
	public void struct() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("struct.cvl")));
	}

	@Test
	public void structArray() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("structArray.cvl")));
	}

	@Test
	public void structStruct() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("structStruct.cvl")));
	}

	@Test
	public void switchBlock() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("switch.cvl")));
	}

	@Test
	public void union() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("union.cvl")));
	}

	@Test
	public void enum1() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("enum1.cvl")));
	}

	@Test
	public void enum2() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, filename("enum2.cvl")));
	}

	@Test
	public void functionPointer() throws ABCException {
		assertTrue(ui.run(VERIFY, NO_PRINTF, QUIET,
				filename("functionPointer.cvl")));
	}

	@Test
	public void undefPointer() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("undefPointer.cvl")));
	}

	@Test
	public void undefHeapPointer() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("undefHeapPointer.cvl")));
	}

	@Test
	public void sideEffectLoop() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("sideEffectLoop.cvl")));
	}

	@Test
	public void assignInput() throws ABCException {
		assertFalse(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("assignInput.cvl")));
	}

	@Test
	public void inputBad() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("inputBad.cvl")));
	}

	@Test
	public void outputBad() throws ABCException {
		assertFalse(ui.run("verify -errorBound=5", QUIET,
				filename("outputBad.cvl")));
	}

	@Test
	public void procNull() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("procNull.cvl")));
	}

	@Test
	public void functionBad() throws ABCException {
		assertFalse(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("functionBad.cvl")));
	}

	@Test
	public void intToBool() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF, filename("intToBool.cvl")));
	}

	@Test
	public void twoDpointerTest() throws ABCException {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("2dpointerTest.cvl")));
	}

	@Test
	public void memoryLeak() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("memoryLeak.cvl")));
	}

	@Test
	public void processLeak() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2), QUIET,
				filename("processLeak.cvl")));
	}

	@Test
	public void comma() throws ABCException {
		assertTrue(ui.run(VERIFY, "-inputn=5", QUIET, filename("comma.cvl")));
	}

	@Test
	public void assignIntWtReal() {
		assertTrue(ui.run(VERIFY, QUIET, filename("assignIntWtReal.cvl")));
	}

	@Test
	public void civlPragma() throws ABCException {
		assertTrue(ui.run(VERIFY, "-inputNB=5", QUIET,
				filename("civlPragma.cvl")));
	}

	@Test
	public void civlFor() throws ABCException {
		assertTrue(ui.run(VERIFY, NO_PRINTF, QUIET, filename("civlfor.cvl")));
	}

	@Test
	public void civlParfor() throws ABCException {
		assertTrue(
				ui.run(VERIFY, NO_PRINTF, QUIET, filename("civlParfor.cvl")));
	}

	@Test
	public void civlParforNotConcrete() throws ABCException {
		assertFalse(ui.run(VERIFY, errorBound(2), NO_PRINTF, QUIET,
				filename("civlParforNotConcrete.cvl")));
	}

	@Test
	public void pointerSub() {
		assertTrue(ui.run(VERIFY, QUIET, filename("pointerSubtraction.cvl")));
	}

	@Test
	public void pointerSubBad() {
		assertFalse(
				ui.run(VERIFY, QUIET, filename("pointerSubtractionBad.cvl")));
	}

	@Test
	public void pointerSubBad2() {
		assertFalse(
				ui.run(VERIFY, QUIET, filename("pointerSubtractionBad2.cvl")));
	}

	@Test
	public void stringTest() {
		assertTrue(ui.run(VERIFY, QUIET, filename("stringTest.cvl")));
	}

	@Test
	public void int2char() {
		assertTrue(ui.run(VERIFY, QUIET, filename("int2char.cvl")));
	}

	@Test
	public void int2charBad() {
		assertFalse(ui.run(VERIFY, QUIET, filename("int2charBad.cvl")));
	}

	@Test
	public void int2charBad2() {
		assertFalse(ui.run(VERIFY, QUIET, filename("int2charBad2.cvl")));
	}

	@Test
	public void include1() {
		assertFalse(
				ui.run(VERIFY, QUIET, "-userIncludePath=" + rootDir.getPath(),
						filename("include1.cvl")));
	}

	@Test
	public void procBound() {
		assertFalse(ui.run(VERIFY, TestConstants.procBound(10), QUIET,
				filename("procBound.cvl")));
	}

	@Test
	public void not() {
		assertTrue(ui.run(VERIFY, QUIET, filename("not.cvl")));
	}

	@Test
	public void noopBad() {
		assertFalse(ui.run(VERIFY, QUIET, "-intOperationTransformer=true",
				filename("noopBad.cvl")));
	}

	@Test
	public void pointerAdd1() {
		// assertTrue(ui.run(VERIFY, QUIET, filename("pointerAdd1.cvl")));
		assertFalse(ui.run("verify", "-DWRONG -verbose=false", QUIET,
				filename("pointerAdd1.cvl")));
		// assertTrue(ui
		// .run(VERIFY, "-DARRAY", QUIET, filename("pointerAdd1.cvl")));
		// assertFalse(ui.run(VERIFY, "-DARRAY -DWRONG", QUIET,
		// filename("pointerAdd1.cvl")));
	}

	@Test
	public void int2float() {
		assertTrue(ui.run(VERIFY, QUIET, filename("int2float.cvl")));
	}

	@Test
	public void initVal() throws ABCException {
		assertFalse(ui.run(VERIFY, QUIET, filename("initialValues.cvl")));
	}

	@Test
	public void valueUndefinedTest() {
		assertFalse(ui.run(VERIFY, errorBound(10), QUIET,
				filename("civlValueUndefined.cvl")));
	}

	@Test
	public void staticVar() {
		assertTrue(ui.run(VERIFY, QUIET, filename("staticVar.cvl")));
	}

	@Test
	public void libraryException() {
		assertFalse(ui.run(VERIFY, errorBound(3),
				"-userIncludePath=examples/library/foo", QUIET,
				filename("libraryException.cvl")));
	}

	@Test
	public void conditionalLHS() {
		assertTrue(ui.run(VERIFY, QUIET, filename("condLHS.c")));
	}

	@Test
	public void intToPointer() {
		assertTrue(ui.run(VERIFY, QUIET, filename("intToPointer.cvl")));
	}

	@Test
	public void splitFormat() {
		assertTrue(
				ui.run(VERIFY, QUIET, NO_PRINTF, filename("splitFormat.cvl")));
	}

	@Test
	public void splitFormatBad() {
		assertFalse(ui.run(VERIFY, QUIET, filename("splitFormatBad.cvl")));
	}

	@Test
	public void splitFormatBad2() {
		assertFalse(ui.run(VERIFY, QUIET, filename("splitFormatBad2.cvl")));
	}

	@Test
	public void splitFormatBad3() {
		assertFalse(ui.run(VERIFY, QUIET, filename("splitFormatBad3.cvl")));
	}

	@Test
	public void atomicFunctionSpecifier() {
		assertTrue(ui.run(VERIFY, QUIET, NO_PRINTF,
				filename("atomicFunctionSpecifier.cvl")));
	}

	@Test
	public void shortCircuit() {
		assertTrue(ui.run(VERIFY, QUIET, filename("shortCircuit.c")));
	}

	@Test
	public void inputProblem() {
		assertTrue(ui.run(VERIFY, "-showProgram", filename("inputProblem1.cvl"),
				filename("inputProblem2.cvl")));
	}

	@Test
	public void imNoMain() throws CIVLSyntaxException {
		assertFalse(ui.run(VERIFY, QUIET, filename("imNoMain.c")));
	}

	@Test
	public void typedefRemoverBug() {
		assertTrue(ui.run(VERIFY, filename("typedefbugMain.c"),
				filename("typedefbugSource.c")));
	}

	@Test
	public void compoundRange_compoundUpperBound() {
		assertTrue(ui.run(VERIFY, QUIET, filename("compoundRange.c")));
	}

	@Test
	public void equals_ignore_qualifiers() {
		assertTrue(ui.run(VERIFY, QUIET, filename("equivQualifier.c")));
	}

	@Test
	public void equals_ignore_qualifiers_bad() {
		assertFalse(ui.run(VERIFY, QUIET, filename("equivQualifier_bad.c")));
	}

	@Test
	public void quantifiedConditionalExpression() {
		assertTrue(ui.run(VERIFY, "-showProverQueries", QUIET,
				filename("quantifiedConditionalExpression.cvl")));
	}

	@Test
	public void ranges() {
		assertTrue(ui.run(VERIFY, QUIET, filename("ranges.cvl")));
	}

	@Test
	public void incompleteStruct() {
		assertTrue(
				ui.run(VERIFY, "-showProgram", filename("incompleteStruct.c")));
	}

	@Test
	public void sizeofTest() {
		assertTrue(ui.run(VERIFY, filename("sizeofTest.cvl")));
	}

	@Test
	public void sizeofBadTest() {
		assertFalse(ui.run(VERIFY, filename("sizeofTestBad.cvl")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
