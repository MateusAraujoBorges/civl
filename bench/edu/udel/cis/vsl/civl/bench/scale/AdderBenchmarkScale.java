package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the adder example. Execution time should be within 20 to 58
 * seconds.
 * 
 * @author zmanchun
 * 
 */
public class AdderBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int i = 2; i <= 14; i++) {
			System.out.println(">>>>>>>> Adder <<<<<<<<");
			ui.run("verify -inputB=" + i + " " + civlDir
					+ "/examples/concurrency/adder.cvl");
		}
	}

	/*
	 * 
	 * >>>>>>>> Adder <<<<<<<<
	 * 
	 * civl verify -inputB=12 ./examples/concurrency/adder.cvl
	 * 
	 * === Stats === time (s) : 4.15
	 * 
	 * civl verify -inputB=13 ./examples/concurrency/adder.cvl
	 * 
	 * === Stats === time (s) : 8.68
	 * 
	 * civl verify -inputB=14 ./examples/concurrency/adder.cvl
	 * 
	 * === Stats === time (s) : 19.45
	 */
}
