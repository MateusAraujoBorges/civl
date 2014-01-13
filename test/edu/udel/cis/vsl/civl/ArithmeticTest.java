package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.UserInterface;

public class ArithmeticTest {

	/************************* Static Fields *************************/

	private static UserInterface ui = new UserInterface();

	private static File rootDir = new File(new File("examples"), "arithmetic");

	/************************* Helper Methods *************************/

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	private void check(String name) {
		assertTrue(ui.run("verify", filename(name)));
	}

	/************************* Test Methods *************************/

	@Test
	public void algebra() {
		check("algebra.cvl");
	}

	@Test
	public void assoc() {
		assertTrue(ui.run("verify", "-inputB=10", filename("assoc.cvl")));
	}

	@Test
	public void derivative() {
		check("derivative.cvl");
	}

	@Test
	public void diffusion() {
		check("diffusion.cvl");
	}

	@Test
	public void division() {
		check("division.cvl");
	}

	@Test
	public void divisionBad() {
		assertFalse(ui.run("verify", filename("divisionBad.cvl")));
	}

	@Test
	public void laplace() {
		check("laplace.cvl");
	}

	@Test
	public void matmat() {
		assertTrue(ui.run("verify", "-inputBOUND=3", "-simplify=false",
				filename("matmat.cvl")));
	}

	@Test
	public void matmatBad() {
		assertFalse(ui
				.run("verify", "-inputBOUND=3", filename("matmatBad.cvl")));
	}

	@Test
	public void mean() {
		assertTrue(ui.run("verify", "-inputB=10", filename("mean.cvl")));
	}

	@Test
	public void meanBad() {
		assertFalse(ui.run("verify", "-inputB=10", "-min",
				filename("meanBad.cvl")));
	}

}
