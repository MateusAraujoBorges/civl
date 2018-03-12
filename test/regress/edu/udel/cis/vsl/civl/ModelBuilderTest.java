package edu.udel.cis.vsl.civl;

import static edu.udel.cis.vsl.civl.TestConstants.QUIET;
import static edu.udel.cis.vsl.civl.TestConstants.VERIFY;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ModelBuilderTest {
	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"),
			"modelbuilder");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */
	@Test
	public void arrayext() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayext.c")));
	}

	@Test
	public void arrayLambda() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayLambda.cvl")));
	}

	@Test
	public void forall() {
		assertTrue(ui.run(VERIFY, QUIET, filename("foralltest.cvl")));
	}

	@Test
	public void arrayLiteral() {
		assertTrue(ui.run(VERIFY, QUIET, filename("arrayLiteral.cvl")));
	}

	@Test
	public void copyArrayLiteral() {
		assertTrue(ui.run(VERIFY, QUIET, filename("copyArrayLiteral.cvl")));
	}

	@Test
	public void stateFunction() {
		assertTrue(ui.run(VERIFY, QUIET, filename("stateFunction.cvl")));
	}

	@Test
	public void boolcast() {
		assertTrue(ui.run(VERIFY, QUIET, filename("boolcast.cvl")));
	}

	@Test
	public void ternaryExpression() {
		assertTrue(ui.run(VERIFY, QUIET, filename("ternary.cvl")));
	}

	@Test
	public void blockScopeExtern() {
		assertTrue(ui.run(VERIFY, QUIET,
				filename("block_scope_extern.c")));
	}

	@Test
	public void blockScopeExtern2() {
		assertTrue(ui.run(VERIFY, QUIET, filename("block_scope_extern2.c")));
	}

	@Test
	public void blockScopeExtern2Bad() {
		assertFalse(
				ui.run(VERIFY, QUIET, filename("block_scope_extern2-bad.c")));
	}

	@Test
	public void fileScopeExtern() {
		assertTrue(
				ui.run(VERIFY, QUIET, filename("file_scope_extern.c")));
	}

	@Test
	public void fileScopeExtern2() {
		assertTrue(ui.run(VERIFY, QUIET, filename("file_scope_extern2.c")));
	}

	@Test
	public void fileScopeExtern3() {
		assertTrue(ui.run(VERIFY, QUIET, filename("file_scope_extern3.c"),
				filename("file_scope_extern3_lib.c")));
	}

	@Test
	public void fileScopeExtern4() {
		assertTrue(
				ui.run(VERIFY, QUIET, filename("file_scope_extern4.c"),
						filename("file_scope_extern4_lib.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
