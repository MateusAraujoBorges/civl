package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class ConcurrencyTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "concurrency");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void adder() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-inputB=5", filename("adder.cvl")));
	}

	@Test
	public void adderBad() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputB=4", 
				TestConstants.MIN, TestConstants.QUIET,
				filename("adderBad.cvl")));
		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.QUIET,
				filename("adderBad.cvl")));
	}

	@Test
	public void bank() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-inputNUM_ACCOUNTS=3", filename("bank.cvl")));
	}

	@Test
	public void barrier() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-inputB=4", filename("barrier.cvl")));
	}

	@Test
	public void barrier2() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-inputB=4", filename("barrier2.cvl")));
	}

	@Test
	public void barrierBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				TestConstants.MIN, "-inputB=4",
				filename("barrierBad.cvl")));
		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.QUIET, 
				"-id=0", filename("barrierBad.cvl")));
	}

	@Test
	public void blockAdder() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				"-inputB=6", "-inputW=3",
				filename("blockAdder.cvl")));
	}

	@Test
	public void blockAdderBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				"-inputB=6", "-inputW=3", TestConstants.MIN,
				filename("blockAdderBad.cvl")));
		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.QUIET,
				filename("blockAdderBad.cvl")));
	}

	@Test
	public void dining() {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputBOUND=4",
				TestConstants.NO_SHOW_TRANSITIONS, TestConstants.QUIET,
				filename("dining.cvl")));
	}

	@Test
	public void diningBad() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputB=4", TestConstants.QUIET,
				TestConstants.MIN,filename("diningBad.cvl")));
		
		assertFalse(ui.run(TestConstants.REPLAY, TestConstants.QUIET,
				filename("diningBad.cvl")));
	}

	@Test
	public void locksBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET,
				filename("locksBad.cvl")));
	}

	@Test
	public void locksBad10() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, filename("locksBad10.cvl")));
	}

	@Test
	public void locksGood() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, filename("locksGood.cvl")));
	}

	@Test
	public void spawn() {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputN=10", 
				TestConstants.QUIET, filename("spawn.cvl")));
	}

	@Test
	public void spawn2() {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputN=10", 
				TestConstants.QUIET, filename("spawn2.cvl")));
	}

	@Test
	public void spawnBad() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputN=10", 
				TestConstants.QUIET, filename("spawnBad.cvl")));
	}

	@Test
	public void waitSelf() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("waitSelf.cvl")));
	}

	@Test
	public void dlqueue() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("dlqueue.cvl")));
	}

	@Test
	public void hybrid() {
		assertFalse(ui.run(TestConstants.VERIFY, "-inputNPROCS=2", 
				TestConstants.QUIET, filename("hybrid.cvl")));
	}

	@Test
	public void mpiPthreads() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.QUIET, 
				filename("mpi-pthreads.cvl")));
	}

	@Test
	public void mpiPthreadsMin() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.MIN, TestConstants.QUIET, 
				TestConstants.QUIET, filename("mpi-pthreads.cvl")));
	}

	@Test
	public void ring() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK, TestConstants.QUIET, 
				" -inputNPROCS_BOUND=8", "-inputN_BOUND=4", filename("ring.cvl")));
	}

	@Test
	public void ring1Bad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK, TestConstants.QUIET, 
				"-inputNPROCS=3", filename("ring1Bad.cvl")));
	}

	@Test
	public void ring1() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK,TestConstants.QUIET, 
				"-inputNPROCS=3", filename("ring1.cvl")));
	}

	@Test
	public void ring2() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK, TestConstants.QUIET,
				"-inputNPROCS=3", filename("ring2.cvl")));
	}

	@Test
	public void ring2Bad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK, TestConstants.QUIET,
				"-inputNPROCS=3", filename("ring2Bad.cvl")));
	}

	@Test
	public void ring3() {
		assertTrue(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK,
				TestConstants.QUIET, filename("ring3.cvl")));
	}

	@Test
	public void ring3Bad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.POTENTIAL_DEADLOCK,
				TestConstants.QUIET, filename("ring3Bad.cvl")));
	}

	@Test
	public void wildcard() {
		assertTrue(ui.run(TestConstants.VERIFY, "-inputNPROCS=2",
				TestConstants.SHOW_TRANSITIONS, TestConstants.QUIET,
				TestConstants.NO_PRINTF, filename("wildcard.cvl")));
	}

	@Test
	public void wildcardBad() {
		assertFalse(ui.run(TestConstants.VERIFY, TestConstants.NO_PRINTF,
				TestConstants.QUIET, filename("wildcardBad.c")));
		ui.run(TestConstants.REPLAY, TestConstants.QUIET, filename("wildcardBad.c"));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
