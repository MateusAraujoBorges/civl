package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the binary guards example. Execution time should be within 20 to
 * 58 seconds (for N == 300 ? no way).
 * 
 * @author zmanchun
 * 
 */
public class BinaryGuardsBenchmark {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		System.out.println(">>>>>>>> binary guards <<<<<<<<");
		ui.run("verify -inputN=15 "
				+ civlDir + "/examples/bench/binaryGuards.cvl");
	}

}
