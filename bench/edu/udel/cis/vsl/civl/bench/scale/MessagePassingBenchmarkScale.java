package edu.udel.cis.vsl.civl.bench.scale;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * Benchmark of the message passing example. Execution time should be within 20
 * to 58 seconds.
 * 
 * @author zmanchun
 * 
 */
public class MessagePassingBenchmarkScale {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) {
		String civlDir = ".";

		if (args.length > 0)
			civlDir = args[0];
		for (int nx = 1; nx < 4; nx++)
			for (int ny = 1; ny < 5; ny++) {
				if (ny < nx || (nx != 3 && ny == 4))
					continue;
				System.out.println(">>>>>>>> Diffusion2d <<<<<<<<");
				ui.run("verify  -inputNSTEPSB=2 -inputNXB=" + nx + " -inputNYB="
						+ ny + " -inputNPROCSXB=" + nx + " " + "-inputNPROCSYB="
						+ ny + " -enablePrintf=false " + civlDir
						+ "/examples/mpi/diffusion2d.c");
			}
		/*
		 * civl verify -inputNSTEPSB=2 -inputNXB=3 -inputNYB=3 -inputNPROCSXB=3
		 * -inputNPROCSYB=3 -enablePrintf=false ./examples/mpi/diffusion2d.c
		 * 
		 * === Stats === time (s) : 15.16
		 * 
		 * civl verify -inputNSTEPSB=2 -inputNXB=3 -inputNYB=4 -inputNPROCSXB=3
		 * -inputNPROCSYB=4 -enablePrintf=false ./examples/mpi/diffusion2d.c
		 * 
		 * === Stats === time (s) : 21.09
		 */
	}

}
